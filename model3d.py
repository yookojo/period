"""glTF / GLB inspect + rig helpers for Period.

Reads and writes glTF 2.0 (.glb / .gltf) without Blender. FBX/OBJ/DAE convert
when Blender is installed. Designed so the agent can inspect skeletons,
animations, and retarget Mixamo-style names onto Roblox R15.
"""

from __future__ import annotations

import json
import os
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

COMPONENT_SIZES = {
    5120: 1,  # BYTE
    5121: 1,  # UNSIGNED_BYTE
    5122: 2,  # SHORT
    5123: 2,  # UNSIGNED_SHORT
    5125: 4,  # UNSIGNED_INT
    5126: 4,  # FLOAT
}
TYPE_COUNTS = {
    "SCALAR": 1,
    "VEC2": 2,
    "VEC3": 3,
    "VEC4": 4,
    "MAT2": 4,
    "MAT3": 9,
    "MAT4": 16,
}
PACK = {
    5120: "b",
    5121: "B",
    5122: "h",
    5123: "H",
    5125: "I",
    5126: "f",
}

# Mixamo (with or without mixamorig: prefix) -> Roblox R15 Motor6D names.
# First matching candidate that exists on the model wins (avoids Spine+Spine1
# both becoming UpperTorso).
R15_FROM_MIXAMO = {
    "LowerTorso": ("hips", "pelvis"),
    "UpperTorso": ("spine2", "chest", "spine1", "spine"),
    "Head": ("head",),
    "LeftUpperArm": ("leftarm", "leftshoulder"),
    "LeftLowerArm": ("leftforearm",),
    "LeftHand": ("lefthand",),
    "RightUpperArm": ("rightarm", "rightshoulder"),
    "RightLowerArm": ("rightforearm",),
    "RightHand": ("righthand",),
    "LeftUpperLeg": ("leftupleg", "leftthigh"),
    "LeftLowerLeg": ("leftleg", "leftshin"),
    "LeftFoot": ("leftfoot",),
    "RightUpperLeg": ("rightupleg", "rightthigh"),
    "RightLowerLeg": ("rightleg", "rightshin"),
    "RightFoot": ("rightfoot",),
}

# Legacy flat map kept for explicit map_nodes({old:new}) callers.
MIXAMO_TO_R15 = {
    "hips": "LowerTorso",
    "spine": "UpperTorso",
    "spine1": "UpperTorso",
    "spine2": "UpperTorso",
    "neck": "Head",
    "head": "Head",
    "leftshoulder": "LeftUpperArm",
    "leftarm": "LeftUpperArm",
    "leftforearm": "LeftLowerArm",
    "lefthand": "LeftHand",
    "rightshoulder": "RightUpperArm",
    "rightarm": "RightUpperArm",
    "rightforearm": "RightLowerArm",
    "righthand": "RightHand",
    "leftupleg": "LeftUpperLeg",
    "leftleg": "LeftLowerLeg",
    "leftfoot": "LeftFoot",
    "lefttoebase": "LeftFoot",
    "rightupleg": "RightUpperLeg",
    "rightleg": "RightLowerLeg",
    "rightfoot": "RightFoot",
    "righttoebase": "RightFoot",
}

R15_BONES = (
    "HumanoidRootPart",
    "LowerTorso",
    "UpperTorso",
    "Head",
    "LeftUpperArm",
    "LeftLowerArm",
    "LeftHand",
    "RightUpperArm",
    "RightLowerArm",
    "RightHand",
    "LeftUpperLeg",
    "LeftLowerLeg",
    "LeftFoot",
    "RightUpperLeg",
    "RightLowerLeg",
    "RightFoot",
)

PRESETS = {
    "mixamo_r15": MIXAMO_TO_R15,
}


class Model3DError(Exception):
    pass


def _require_pygltflib():
    try:
        from pygltflib import GLTF2  # noqa: F401
        return True
    except ImportError as e:
        raise Model3DError(
            "pygltflib is not installed. Run: pip install pygltflib"
        ) from e


def load_gltf(path):
    _require_pygltflib()
    from pygltflib import GLTF2

    p = Path(path)
    if not p.is_file():
        raise Model3DError(f"file not found: {path}")
    suffix = p.suffix.lower()
    if suffix not in (".glb", ".gltf"):
        raise Model3DError(
            f"unsupported 3D format {suffix or '(no extension)'}. "
            "Native tools handle .glb/.gltf. Convert FBX/OBJ/DAE with model3d_convert "
            "(needs Blender) first."
        )
    try:
        gltf = GLTF2().load(str(p))
        gltf._remote_path = p
        return gltf
    except Exception as e:
        raise Model3DError(f"could not parse {p.name}: {e}") from e


def save_gltf(gltf, path):
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    suffix = p.suffix.lower()
    try:
        if suffix == ".glb":
            if hasattr(gltf, "save_binary"):
                gltf.save_binary(str(p))
            else:
                gltf.save(str(p))
        else:
            if suffix != ".gltf":
                p = p.with_suffix(".gltf")
            gltf.save(str(p))
    except Exception as e:
        raise Model3DError(f"could not write {p}: {e}") from e
    return p


def find_blender():
    found = shutil.which("blender")
    if found:
        return found
    candidates = []
    if sys.platform == "win32":
        for root in (
            os.environ.get("ProgramFiles", r"C:\Program Files"),
            os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"),
            os.environ.get("LOCALAPPDATA", ""),
        ):
            if not root:
                continue
            try:
                from glob import glob
                candidates.extend(glob(os.path.join(root, "Blender Foundation", "Blender*", "blender.exe")))
            except Exception:
                pass
    elif sys.platform == "darwin":
        candidates.append("/Applications/Blender.app/Contents/MacOS/Blender")
    for c in sorted(candidates, reverse=True):
        if os.path.isfile(c):
            return c
    return None


def _nodes(gltf):
    return list(gltf.nodes or [])


def _node_name(gltf, index):
    nodes = _nodes(gltf)
    if index is None or index < 0 or index >= len(nodes):
        return f"node_{index}"
    name = getattr(nodes[index], "name", None)
    return name if name else f"node_{index}"


def _children(node):
    kids = getattr(node, "children", None) or []
    return list(kids)


def _strip_bone_key(name):
    n = (name or "").strip()
    if ":" in n:
        n = n.split(":", 1)[1]
    return n.replace(" ", "").replace("_", "").replace("-", "").lower()


def _buffer_data(gltf, buffer_index):
    buffers = gltf.buffers or []
    if buffer_index is None or buffer_index < 0 or buffer_index >= len(buffers):
        return b""
    buf = buffers[buffer_index]
    uri = getattr(buf, "uri", None)
    if not uri:
        blob = None
        if hasattr(gltf, "binary_blob"):
            try:
                blob = gltf.binary_blob()
            except Exception:
                blob = None
        if blob:
            return blob
        return getattr(gltf, "_glb_data", None) or b""
    if uri.startswith("data:"):
        import base64
        try:
            return base64.b64decode(uri.split(",", 1)[1])
        except Exception:
            return b""
    src = getattr(gltf, "_remote_path", None)
    base = Path(src).parent if src else Path(".")
    target = (base / uri).resolve()
    if target.is_file():
        return target.read_bytes()
    return b""


def _unpack_accessor(gltf, accessor_index):
    accessors = gltf.accessors or []
    if accessor_index is None or accessor_index < 0 or accessor_index >= len(accessors):
        return []
    acc = accessors[accessor_index]
    bvi = getattr(acc, "bufferView", None)
    if bvi is None:
        return []
    views = gltf.bufferViews or []
    if bvi < 0 or bvi >= len(views):
        return []
    view = views[bvi]
    data = _buffer_data(gltf, getattr(view, "buffer", 0) or 0)
    offset = (getattr(view, "byteOffset", 0) or 0) + (getattr(acc, "byteOffset", 0) or 0)
    ctype = getattr(acc, "componentType", 5126)
    tname = getattr(acc, "type", "SCALAR")
    count = getattr(acc, "count", 0) or 0
    ncomp = TYPE_COUNTS.get(tname, 1)
    csize = COMPONENT_SIZES.get(ctype, 4)
    fmt = "<" + (PACK.get(ctype, "f") * ncomp)
    stride = getattr(view, "byteStride", None) or (csize * ncomp)
    out = []
    for i in range(count):
        start = offset + i * stride
        chunk = data[start:start + csize * ncomp]
        if len(chunk) < csize * ncomp:
            break
        vals = struct.unpack(fmt, chunk)
        out.append(vals[0] if ncomp == 1 else vals)
    return out


def _mat_ident():
    return [
        [1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
    ]


def _mat_mul(a, b):
    out = [[0.0] * 4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            out[i][j] = (
                a[i][0] * b[0][j] + a[i][1] * b[1][j]
                + a[i][2] * b[2][j] + a[i][3] * b[3][j]
            )
    return out


def _mat_from_translation(x, y, z):
    m = _mat_ident()
    m[0][3], m[1][3], m[2][3] = float(x), float(y), float(z)
    return m


def _mat_from_scale(x, y, z):
    m = _mat_ident()
    m[0][0], m[1][1], m[2][2] = float(x), float(y), float(z)
    return m


def _mat_from_quat(x, y, z, w):
    x, y, z, w = float(x), float(y), float(z), float(w)
    xx, yy, zz = x * x, y * y, z * z
    xy, xz, yz = x * y, x * z, y * z
    wx, wy, wz = w * x, w * y, w * z
    m = _mat_ident()
    m[0][0] = 1 - 2 * (yy + zz)
    m[0][1] = 2 * (xy - wz)
    m[0][2] = 2 * (xz + wy)
    m[1][0] = 2 * (xy + wz)
    m[1][1] = 1 - 2 * (xx + zz)
    m[1][2] = 2 * (yz - wx)
    m[2][0] = 2 * (xz - wy)
    m[2][1] = 2 * (yz + wx)
    m[2][2] = 1 - 2 * (xx + yy)
    return m


def _mat_from_column_major(cols):
    if not cols or len(cols) < 16:
        return _mat_ident()
    m = _mat_ident()
    for c in range(4):
        for r in range(4):
            m[r][c] = float(cols[c * 4 + r])
    return m


def _mat_to_column_major(m):
    out = []
    for c in range(4):
        for r in range(4):
            out.append(float(m[r][c]))
    return out


def _mat_invert(m):
    a = [row[:] + [1.0 if i == j else 0.0 for j in range(4)] for i, row in enumerate(m)]
    for col in range(4):
        pivot = col
        best = abs(a[col][col])
        for r in range(col + 1, 4):
            if abs(a[r][col]) > best:
                best = abs(a[r][col])
                pivot = r
        if best < 1e-12:
            return _mat_ident()
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
        div = a[col][col]
        a[col] = [v / div for v in a[col]]
        for r in range(4):
            if r == col:
                continue
            factor = a[r][col]
            a[r] = [a[r][c] - factor * a[col][c] for c in range(8)]
    return [row[4:] for row in a]


def _node_local_matrix(node):
    raw = getattr(node, "matrix", None)
    if raw:
        return _mat_from_column_major(raw)
    t = getattr(node, "translation", None) or [0, 0, 0]
    r = getattr(node, "rotation", None) or [0, 0, 0, 1]
    s = getattr(node, "scale", None) or [1, 1, 1]
    return _mat_mul(
        _mat_from_translation(t[0], t[1], t[2]),
        _mat_mul(_mat_from_quat(r[0], r[1], r[2], r[3]), _mat_from_scale(s[0], s[1], s[2])),
    )


def _parent_index_map(gltf):
    parent = {}
    for i, node in enumerate(_nodes(gltf)):
        for c in _children(node):
            parent[c] = i
    return parent


def _node_world_matrix(gltf, index, cache=None):
    if cache is not None and index in cache:
        return cache[index]
    nodes = _nodes(gltf)
    if index is None or index < 0 or index >= len(nodes):
        return _mat_ident()
    parent_of = _parent_index_map(gltf)
    local = _node_local_matrix(nodes[index])
    p = parent_of.get(index)
    world = local if p is None else _mat_mul(_node_world_matrix(gltf, p, cache), local)
    if cache is not None:
        cache[index] = world
    return world


def _transform_point(m, x, y, z):
    return (
        m[0][0] * x + m[0][1] * y + m[0][2] * z + m[0][3],
        m[1][0] * x + m[1][1] * y + m[1][2] * z + m[1][3],
        m[2][0] * x + m[2][1] * y + m[2][2] * z + m[2][3],
    )


def _write_blob(gltf, blob):
    from pygltflib import Buffer

    blob = bytes(blob)
    if hasattr(gltf, "set_binary_blob"):
        gltf.set_binary_blob(blob)
    else:
        gltf._glb_data = blob
    if not gltf.buffers:
        gltf.buffers = [Buffer()]
    gltf.buffers[0].byteLength = len(blob)
    gltf.buffers[0].uri = None


def _append_accessor(gltf, packed, component_type, type_name, count, mins=None, maxs=None):
    from pygltflib import Accessor, BufferView

    blob = bytearray(_buffer_data(gltf, 0) or b"")
    while len(blob) % 4:
        blob.append(0)
    offset = len(blob)
    blob.extend(packed)
    while len(blob) % 4:
        blob.append(0)
    _write_blob(gltf, bytes(blob))
    if gltf.bufferViews is None:
        gltf.bufferViews = []
    if gltf.accessors is None:
        gltf.accessors = []
    gltf.bufferViews.append(BufferView(buffer=0, byteOffset=offset, byteLength=len(packed)))
    view_i = len(gltf.bufferViews) - 1
    acc = Accessor(
        bufferView=view_i,
        componentType=component_type,
        count=count,
        type=type_name,
    )
    if mins is not None:
        acc.min = list(mins)
    if maxs is not None:
        acc.max = list(maxs)
    gltf.accessors.append(acc)
    return len(gltf.accessors) - 1


def _scene_roots(gltf):
    roots = []
    for scene in gltf.scenes or []:
        roots.extend(getattr(scene, "nodes", None) or [])
    if roots:
        return roots
    child_set = set()
    nodes = _nodes(gltf)
    for node in nodes:
        child_set.update(_children(node))
    return [i for i in range(len(nodes)) if i not in child_set]


def _find_named(gltf, name):
    key = _strip_bone_key(name)
    for i in range(len(_nodes(gltf))):
        if _strip_bone_key(_node_name(gltf, i)) == key:
            return i
    return None


def _unique_mixamo_map(gltf):
    """Pick at most one source bone per R15 name."""
    by_key = {}
    for i in range(len(_nodes(gltf))):
        by_key.setdefault(_strip_bone_key(_node_name(gltf, i)), []).append(i)
    mapping = {}
    used_nodes = set()
    for r15, candidates in R15_FROM_MIXAMO.items():
        existing = _find_named(gltf, r15)
        if existing is not None:
            if _node_name(gltf, existing) != r15:
                mapping[existing] = r15
            used_nodes.add(existing)
            continue
        for cand in candidates:
            hits = [idx for idx in by_key.get(cand, []) if idx not in used_nodes]
            if not hits:
                continue
            mapping[hits[0]] = r15
            used_nodes.add(hits[0])
            break
    return mapping


def _apply_unique_r15_names(gltf):
    mapping = _unique_mixamo_map(gltf)
    renamed = []
    for idx, new in mapping.items():
        old = _node_name(gltf, idx)
        gltf.nodes[idx].name = new
        renamed.append(f"{old} -> {new}")
    return renamed


def inspect_model(path):
    gltf = load_gltf(path)
    p = Path(path)
    nodes = _nodes(gltf)
    meshes = list(gltf.meshes or [])
    skins = list(gltf.skins or [])
    anims = list(gltf.animations or [])
    mats = list(gltf.materials or [])
    images = list(gltf.images or [])
    scenes = list(gltf.scenes or [])
    skinned_meshes = 0
    for mesh in meshes:
        for prim in getattr(mesh, "primitives", None) or []:
            attrs = getattr(prim, "attributes", None)
            if attrs is not None and getattr(attrs, "JOINTS_0", None) is not None:
                skinned_meshes += 1
                break
    asset = getattr(gltf, "asset", None)
    generator = getattr(asset, "generator", None) if asset else None
    lines = [
        f"file: {p.name} ({p.suffix.lower()}, {p.stat().st_size} bytes)",
        f"generator: {generator or '(unknown)'}",
        f"scenes: {len(scenes)}  nodes: {len(nodes)}  meshes: {len(meshes)}  "
        f"skinned_meshes: {skinned_meshes}",
        f"materials: {len(mats)}  images: {len(images)}  skins: {len(skins)}  "
        f"animations: {len(anims)}",
    ]
    if skins:
        lines.append("skins:")
        for i, skin in enumerate(skins):
            joints = list(getattr(skin, "joints", None) or [])
            lines.append(
                f"  [{i}] {getattr(skin, 'name', None) or f'skin_{i}'}  "
                f"joints={len(joints)}  skeleton={getattr(skin, 'skeleton', None)}"
            )
    if anims:
        lines.append("animations:")
        for i, anim in enumerate(anims):
            ch = list(getattr(anim, "channels", None) or [])
            lines.append(
                f"  [{i}] {getattr(anim, 'name', None) or f'clip_{i}'}  channels={len(ch)}"
            )
    return "\n".join(lines)


def hierarchy(path):
    gltf = load_gltf(path)
    nodes = _nodes(gltf)
    scenes = list(gltf.scenes or [])
    mentioned = set()
    lines = []

    def walk(idx, depth):
        if idx is None or idx < 0 or idx >= len(nodes) or idx in mentioned:
            return
        mentioned.add(idx)
        node = nodes[idx]
        extra = []
        if getattr(node, "mesh", None) is not None:
            extra.append(f"mesh={node.mesh}")
        if getattr(node, "skin", None) is not None:
            extra.append(f"skin={node.skin}")
        trs = []
        if getattr(node, "translation", None):
            t = node.translation
            trs.append(f"t=({t[0]:.3g},{t[1]:.3g},{t[2]:.3g})")
        tag = (" " + " ".join(extra + trs)) if (extra or trs) else ""
        lines.append(f"{'  ' * depth}{idx}: {_node_name(gltf, idx)}{tag}")
        for child in _children(node):
            walk(child, depth + 1)

    roots = []
    for scene in scenes:
        roots.extend(getattr(scene, "nodes", None) or [])
    if not roots:
        child_set = set()
        for node in nodes:
            child_set.update(_children(node))
        roots = [i for i in range(len(nodes)) if i not in child_set]
    for r in roots:
        walk(r, 0)
    for i in range(len(nodes)):
        if i not in mentioned:
            walk(i, 0)
    return "\n".join(lines) if lines else "(no nodes)"


def rig_report(path):
    gltf = load_gltf(path)
    nodes = _nodes(gltf)
    skins = list(gltf.skins or [])
    if not skins:
        return "No skins (armatures) on this model. Meshes are not rigged."
    lines = []
    for si, skin in enumerate(skins):
        joints = list(getattr(skin, "joints", None) or [])
        skel = getattr(skin, "skeleton", None)
        lines.append(
            f"skin[{si}] {getattr(skin, 'name', None) or ''}  "
            f"skeleton={skel} ({_node_name(gltf, skel) if skel is not None else '-'})  "
            f"{len(joints)} joints"
        )
        parent_of = {}
        for i, node in enumerate(nodes):
            for c in _children(node):
                parent_of[c] = i
        for ji, joint in enumerate(joints):
            parent = parent_of.get(joint)
            parent_s = _node_name(gltf, parent) if parent is not None else "(root)"
            lines.append(f"  {ji:3d}  {_node_name(gltf, joint):<28}  parent={parent_s}")
    meshes = list(gltf.meshes or [])
    lines.append("skinned primitives:")
    found = False
    for mi, mesh in enumerate(meshes):
        for pi, prim in enumerate(getattr(mesh, "primitives", None) or []):
            attrs = getattr(prim, "attributes", None)
            if attrs is None:
                continue
            j = getattr(attrs, "JOINTS_0", None)
            w = getattr(attrs, "WEIGHTS_0", None)
            if j is None and w is None:
                continue
            found = True
            lines.append(
                f"  mesh[{mi}] {getattr(mesh, 'name', None) or ''} prim[{pi}] "
                f"JOINTS_0={j} WEIGHTS_0={w}"
            )
    if not found:
        lines.append("  (no JOINTS_0 / WEIGHTS_0 attributes — skin may be unused)")
    return "\n".join(lines)


def _sampler_duration(gltf, sampler):
    inp = getattr(sampler, "input", None)
    times = _unpack_accessor(gltf, inp) if inp is not None else []
    if not times:
        return 0.0
    last = times[-1]
    return float(last if isinstance(last, (int, float)) else last[0])


def animations_report(path):
    gltf = load_gltf(path)
    anims = list(gltf.animations or [])
    if not anims:
        return "No animations."
    lines = []
    for i, anim in enumerate(anims):
        samplers = list(getattr(anim, "samplers", None) or [])
        channels = list(getattr(anim, "channels", None) or [])
        dur = 0.0
        for s in samplers:
            dur = max(dur, _sampler_duration(gltf, s))
        lines.append(
            f"[{i}] {getattr(anim, 'name', None) or f'clip_{i}'}  "
            f"duration={dur:.3f}s  channels={len(channels)}"
        )
        for ch in channels[:40]:
            target = getattr(ch, "target", None)
            node = getattr(target, "node", None) if target else None
            tpath = getattr(target, "path", None) if target else None
            lines.append(f"    {_node_name(gltf, node)}.{tpath}")
        if len(channels) > 40:
            lines.append(f"    … {len(channels) - 40} more channels")
    return "\n".join(lines)


def validate_model(path):
    gltf = load_gltf(path)
    nodes = _nodes(gltf)
    issues = []
    names = [_node_name(gltf, i) for i in range(len(nodes))]
    dup = {}
    for n in names:
        dup[n] = dup.get(n, 0) + 1
    for n, c in dup.items():
        if c > 1:
            issues.append(f"duplicate node name '{n}' ({c} times)")
    for si, skin in enumerate(gltf.skins or []):
        joints = list(getattr(skin, "joints", None) or [])
        ibm = getattr(skin, "inverseBindMatrices", None)
        if ibm is None:
            issues.append(f"skin[{si}] has no inverseBindMatrices")
        for j in joints:
            if j is None or j < 0 or j >= len(nodes):
                issues.append(f"skin[{si}] joint index {j} is out of range")
    for ai, anim in enumerate(gltf.animations or []):
        for ci, ch in enumerate(getattr(anim, "channels", None) or []):
            target = getattr(ch, "target", None)
            node = getattr(target, "node", None) if target else None
            if node is None:
                issues.append(f"animation[{ai}] channel[{ci}] has no target node")
            elif node < 0 or node >= len(nodes):
                issues.append(f"animation[{ai}] channel[{ci}] targets missing node {node}")
    meshes = list(gltf.meshes or [])
    for mi, mesh in enumerate(meshes):
        for pi, prim in enumerate(getattr(mesh, "primitives", None) or []):
            attrs = getattr(prim, "attributes", None)
            if attrs is None:
                continue
            has_j = getattr(attrs, "JOINTS_0", None) is not None
            has_w = getattr(attrs, "WEIGHTS_0", None) is not None
            if has_j != has_w:
                issues.append(f"mesh[{mi}] prim[{pi}] has JOINTS/WEIGHTS mismatch")
    if not issues:
        return "No rig/animation issues found."
    return "Issues:\n" + "\n".join(f"- {x}" for x in issues)


def roblox_rig_check(path):
    gltf = load_gltf(path)
    present = {}
    for i, node in enumerate(_nodes(gltf)):
        key = _strip_bone_key(_node_name(gltf, i))
        present[key] = _node_name(gltf, i)
    lines = ["Roblox R15 bone check (name match, case-insensitive):"]
    missing = []
    for bone in R15_BONES:
        hit = present.get(_strip_bone_key(bone))
        if hit:
            lines.append(f"  OK   {bone}  (as '{hit}')")
        else:
            missing.append(bone)
            lines.append(f"  MISS {bone}")
    skins = list(gltf.skins or [])
    if not skins:
        lines.append("No skin/armature — Roblox import will not be a rigged character.")
    if missing:
        lines.append(
            f"Missing {len(missing)}/{len(R15_BONES)} R15 names. "
            "Use model3d_map_nodes with preset mixamo_r15 if this is Mixamo."
        )
    else:
        lines.append("All R15 names present.")
    if "humanoidrootpart" not in present:
        lines.append("Note: HumanoidRootPart is missing (often added in Studio, not in the GLB).")
    return "\n".join(lines)


def _resolve_node(gltf, name_or_index):
    nodes = _nodes(gltf)
    if isinstance(name_or_index, int) or (
        isinstance(name_or_index, str) and name_or_index.isdigit()
    ):
        idx = int(name_or_index)
        if 0 <= idx < len(nodes):
            return idx
        raise Model3DError(f"node index {idx} out of range (0-{len(nodes) - 1})")
    want = str(name_or_index)
    want_key = _strip_bone_key(want)
    exact = []
    fuzzy = []
    for i, node in enumerate(nodes):
        n = _node_name(gltf, i)
        if n == want:
            exact.append(i)
        elif _strip_bone_key(n) == want_key:
            fuzzy.append(i)
    hits = exact or fuzzy
    if not hits:
        raise Model3DError(f"no node named {want!r}")
    if len(hits) > 1:
        raise Model3DError(
            f"multiple nodes match {want!r}: " + ", ".join(_node_name(gltf, i) for i in hits)
        )
    return hits[0]


def rename_node(path, node, new_name, out=None):
    gltf = load_gltf(path)
    idx = _resolve_node(gltf, node)
    old = _node_name(gltf, idx)
    gltf.nodes[idx].name = str(new_name)
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    return f"Renamed node {idx} '{old}' -> '{new_name}' in {dest}"


def reparent_node(path, node, parent, out=None):
    gltf = load_gltf(path)
    idx = _resolve_node(gltf, node)
    if parent in ("", None, -1, "root", "none"):
        parent_idx = None
    else:
        parent_idx = _resolve_node(gltf, parent)
        if parent_idx == idx:
            raise Model3DError("cannot parent a node to itself")
    nodes = _nodes(gltf)
    for n in nodes:
        kids = _children(n)
        if idx in kids:
            n.children = [c for c in kids if c != idx] or None
    if parent_idx is not None:
        p = nodes[parent_idx]
        kids = _children(p)
        if idx not in kids:
            kids.append(idx)
        p.children = kids
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    parent_s = _node_name(gltf, parent_idx) if parent_idx is not None else "(scene root)"
    return f"Reparented '{_node_name(gltf, idx)}' under '{parent_s}' in {dest}"


def set_transform(path, node, translation=None, rotation=None, scale=None, out=None):
    gltf = load_gltf(path)
    idx = _resolve_node(gltf, node)
    n = gltf.nodes[idx]
    if translation is not None:
        if len(translation) != 3:
            raise Model3DError("translation must be [x, y, z]")
        n.translation = [float(x) for x in translation]
        n.matrix = None
    if rotation is not None:
        if len(rotation) != 4:
            raise Model3DError("rotation must be quaternion [x, y, z, w]")
        n.rotation = [float(x) for x in rotation]
        n.matrix = None
    if scale is not None:
        if len(scale) != 3:
            raise Model3DError("scale must be [x, y, z]")
        n.scale = [float(x) for x in scale]
        n.matrix = None
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    return f"Updated transform on '{_node_name(gltf, idx)}' in {dest}"


def map_nodes(path, mapping=None, preset=None, out=None):
    if not preset and not mapping:
        raise Model3DError("provide map and/or preset (mixamo_r15)")
    gltf = load_gltf(path)
    renamed = []
    if preset == "mixamo_r15":
        renamed.extend(_apply_unique_r15_names(gltf))
    elif preset:
        raw = PRESETS.get(str(preset))
        if not raw:
            raise Model3DError(
                f"unknown preset {preset!r}. Known: mixamo_r15"
            )
        mapping = dict(raw if mapping is None else {**raw, **mapping})
    if mapping:
        if not isinstance(mapping, dict):
            raise Model3DError("map must be an object of {old_name: new_name}")
        used_targets = {
            _strip_bone_key(_node_name(gltf, i))
            for i in range(len(_nodes(gltf)))
        }
        for i, node in enumerate(_nodes(gltf)):
            current = _node_name(gltf, i)
            key = _strip_bone_key(current)
            new = mapping.get(current) or mapping.get(key)
            if not new:
                continue
            tkey = _strip_bone_key(new)
            if tkey in used_targets and tkey != key:
                continue
            node.name = new
            used_targets.discard(key)
            used_targets.add(tkey)
            renamed.append(f"{current} -> {new}")
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    if not renamed:
        return f"No node names matched the map. Wrote {dest} unchanged."
    return f"Renamed {len(renamed)} nodes in {dest}:\n" + "\n".join(f"  {r}" for r in renamed)


def retarget_animation(path, mapping, out=None, clip=None):
    if not isinstance(mapping, dict) or not mapping:
        raise Model3DError("map must be {from_node: to_node}")
    gltf = load_gltf(path)
    resolved = {}
    for src, dst in mapping.items():
        resolved[_resolve_node(gltf, src)] = _resolve_node(gltf, dst)
    anims = list(gltf.animations or [])
    if clip is not None:
        if isinstance(clip, int) or str(clip).isdigit():
            idxs = [int(clip)]
        else:
            idxs = [
                i for i, a in enumerate(anims)
                if (getattr(a, "name", None) or "") == str(clip)
            ]
            if not idxs:
                raise Model3DError(f"no animation named {clip!r}")
        chosen = idxs
    else:
        chosen = list(range(len(anims)))
    moved = 0
    for ai in chosen:
        for ch in getattr(anims[ai], "channels", None) or []:
            target = getattr(ch, "target", None)
            if target is None:
                continue
            node = getattr(target, "node", None)
            if node in resolved:
                target.node = resolved[node]
                moved += 1
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    return f"Retargeted {moved} animation channels in {dest}"


def compute_ibm(path, out=None):
    """Write inverse bind matrices from each joint's current world matrix."""
    gltf = load_gltf(path)
    written = _compute_ibm_inplace(gltf)
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    return f"Wrote inverse bind matrices for {written} skin(s) in {dest}"


def _compute_ibm_inplace(gltf):
    skins = list(gltf.skins or [])
    if not skins:
        raise Model3DError("no skins to write bind poses for")
    cache = {}
    written = 0
    for skin in skins:
        joints = list(getattr(skin, "joints", None) or [])
        if not joints:
            continue
        packed = b""
        for j in joints:
            world = _node_world_matrix(gltf, j, cache)
            ibm = _mat_invert(world)
            packed += struct.pack("<16f", *_mat_to_column_major(ibm))
        acc = _append_accessor(gltf, packed, 5126, "MAT4", len(joints))
        skin.inverseBindMatrices = acc
        written += 1
    return written


def add_root(path, name="HumanoidRootPart", child=None, out=None):
    """Insert a new root bone above the current skeleton / scene root."""
    from pygltflib import Node

    gltf = load_gltf(path)
    if _find_named(gltf, name) is not None:
        dest = Path(out) if out else Path(path)
        save_gltf(gltf, dest)
        return f"Root '{name}' already exists. Wrote {dest} unchanged."
    if child is not None:
        child_idx = _resolve_node(gltf, child)
    else:
        child_idx = _find_named(gltf, "LowerTorso")
        if child_idx is None:
            child_idx = _find_named(gltf, "Hips")
        if child_idx is None:
            roots = _scene_roots(gltf)
            child_idx = roots[0] if roots else 0
    parent_of = _parent_index_map(gltf)
    old_parent = parent_of.get(child_idx)
    if old_parent is not None:
        pnode = gltf.nodes[old_parent]
        pnode.children = [c for c in _children(pnode) if c != child_idx] or None
    for scene in gltf.scenes or []:
        snodes = list(getattr(scene, "nodes", None) or [])
        if child_idx in snodes:
            scene.nodes = [n for n in snodes if n != child_idx]
    new_idx = len(_nodes(gltf))
    gltf.nodes.append(Node(name=str(name), children=[child_idx]))
    scenes = list(gltf.scenes or [])
    if scenes:
        roots = list(getattr(scenes[0], "nodes", None) or [])
        roots.append(new_idx)
        scenes[0].nodes = roots
    if gltf.skins:
        skin = gltf.skins[0]
        joints = list(getattr(skin, "joints", None) or [])
        if new_idx not in joints:
            joints.append(new_idx)
        skin.joints = joints
        skin.skeleton = new_idx
        skin.inverseBindMatrices = None
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    compute_ibm(dest, out=dest)
    return f"Added root '{name}' (node {new_idx}) above '{_node_name(gltf, child_idx)}' in {dest}"


def auto_skin(path, influences=4, out=None):
    """Assign each mesh vertex to the nearest joints (distance weights)."""
    gltf = load_gltf(path)
    skins = list(gltf.skins or [])
    if not skins:
        from pygltflib import Skin
        joints = [
            i for i, n in enumerate(_nodes(gltf))
            if getattr(n, "mesh", None) is None
        ]
        if len(joints) < 1:
            raise Model3DError("no bone nodes to skin to")
        gltf.skins = [Skin(name="Armature", joints=joints, skeleton=joints[0])]
        skins = gltf.skins
        _compute_ibm_inplace(gltf)
    skin = skins[0]
    joints = list(getattr(skin, "joints", None) or [])
    if not joints:
        raise Model3DError("skin has no joints")
    cache = {}
    joint_pos = []
    for j in joints:
        w = _node_world_matrix(gltf, j, cache)
        joint_pos.append((w[0][3], w[1][3], w[2][3]))
    k = max(1, min(int(influences or 4), 4, len(joints)))
    skinned = 0
    for mi, mesh in enumerate(gltf.meshes or []):
        for prim in getattr(mesh, "primitives", None) or []:
            attrs = getattr(prim, "attributes", None)
            if attrs is None or getattr(attrs, "POSITION", None) is None:
                continue
            positions = _unpack_accessor(gltf, attrs.POSITION)
            if not positions:
                continue
            mesh_node = None
            for ni, node in enumerate(_nodes(gltf)):
                if getattr(node, "mesh", None) == mi:
                    mesh_node = ni
                    if getattr(node, "skin", None) is None:
                        node.skin = 0
                    break
            world = _node_world_matrix(gltf, mesh_node, cache) if mesh_node is not None else _mat_ident()
            joints_bytes = b""
            weights_bytes = b""
            for pos in positions:
                x, y, z = _transform_point(world, pos[0], pos[1], pos[2])
                dists = []
                for ji, (jx, jy, jz) in enumerate(joint_pos):
                    d2 = (x - jx) ** 2 + (y - jy) ** 2 + (z - jz) ** 2
                    dists.append((d2, ji))
                dists.sort()
                picks = dists[:k]
                raw = [1.0 / (d2 + 1e-8) for d2, _ in picks]
                total = sum(raw) or 1.0
                js = [0] * 4
                ws = [0.0] * 4
                for n, ((_, ji), w) in enumerate(zip(picks, raw)):
                    js[n] = ji
                    ws[n] = w / total
                joints_bytes += struct.pack("<4H", *js)
                weights_bytes += struct.pack("<4f", *ws)
            attrs.JOINTS_0 = _append_accessor(gltf, joints_bytes, 5123, "VEC4", len(positions))
            attrs.WEIGHTS_0 = _append_accessor(gltf, weights_bytes, 5126, "VEC4", len(positions))
            skinned += 1
    if not skinned:
        raise Model3DError("no mesh positions to skin")
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    return f"Auto-skinned {skinned} primitive(s) to {len(joints)} joints ({k} influences) in {dest}"


def scale_model(path, factor, out=None):
    factor = float(factor)
    if factor == 0:
        raise Model3DError("scale factor cannot be 0")
    gltf = load_gltf(path)
    for idx in _scene_roots(gltf):
        node = gltf.nodes[idx]
        s = list(getattr(node, "scale", None) or [1, 1, 1])
        node.scale = [s[0] * factor, s[1] * factor, s[2] * factor]
        node.matrix = None
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    return f"Scaled scene roots by {factor} in {dest}"


def ground_model(path, out=None):
    """Shift the model so the lowest mesh vertex sits on Y=0."""
    gltf = load_gltf(path)
    cache = {}
    min_y = None
    for mi, mesh in enumerate(gltf.meshes or []):
        mesh_node = None
        for ni, node in enumerate(_nodes(gltf)):
            if getattr(node, "mesh", None) == mi:
                mesh_node = ni
                break
        world = _node_world_matrix(gltf, mesh_node, cache) if mesh_node is not None else _mat_ident()
        for prim in getattr(mesh, "primitives", None) or []:
            attrs = getattr(prim, "attributes", None)
            if attrs is None or getattr(attrs, "POSITION", None) is None:
                continue
            for pos in _unpack_accessor(gltf, attrs.POSITION):
                _, y, _ = _transform_point(world, pos[0], pos[1], pos[2])
                min_y = y if min_y is None else min(min_y, y)
    if min_y is None:
        raise Model3DError("no mesh positions to ground")
    roots = _scene_roots(gltf)
    if not roots:
        raise Model3DError("no scene root to shift")
    node = gltf.nodes[roots[0]]
    t = list(getattr(node, "translation", None) or [0, 0, 0])
    t[1] = t[1] - min_y
    node.translation = t
    node.matrix = None
    dest = Path(out) if out else Path(path)
    save_gltf(gltf, dest)
    return f"Grounded model (shifted Y by {-min_y:.4g}) in {dest}"


def prepare_r15(path, out=None, skin=True):
    """One-shot Mixamo/generic GLB -> Roblox-oriented R15: unique names, root, IBM, optional auto-skin."""
    dest = Path(out) if out else Path(path)
    gltf = load_gltf(path)
    renamed = _apply_unique_r15_names(gltf)
    save_gltf(gltf, dest)
    notes = []
    if renamed:
        notes.append("renamed " + ", ".join(renamed))
    else:
        notes.append("no Mixamo names to remap")
    notes.append(add_root(dest, name="HumanoidRootPart", out=dest))
    notes.append(compute_ibm(dest, out=dest))
    gltf = load_gltf(dest)
    needs_skin = True
    for mesh in gltf.meshes or []:
        for prim in getattr(mesh, "primitives", None) or []:
            attrs = getattr(prim, "attributes", None)
            if attrs is not None and getattr(attrs, "JOINTS_0", None) is not None:
                needs_skin = False
    if skin and needs_skin:
        notes.append(auto_skin(dest, out=dest))
    notes.append(roblox_rig_check(dest))
    return "prepare_r15:\n" + "\n".join(f"- {n}" for n in notes)


def _export_obj(gltf, dest):
    dest = Path(dest)
    lines = ["# Period OBJ export", "o mesh"]
    v_off = 1
    meshes = list(gltf.meshes or [])
    if not meshes:
        raise Model3DError("no meshes to export")
    for mesh in meshes:
        for prim in getattr(mesh, "primitives", None) or []:
            attrs = getattr(prim, "attributes", None)
            if attrs is None or getattr(attrs, "POSITION", None) is None:
                continue
            positions = _unpack_accessor(gltf, attrs.POSITION)
            for v in positions:
                lines.append(f"v {v[0]} {v[1]} {v[2]}")
            indices = _unpack_accessor(gltf, getattr(prim, "indices", None)) if getattr(prim, "indices", None) is not None else []
            if indices:
                tris = list(indices)
                for i in range(0, len(tris) - 2, 3):
                    a, b, c = int(tris[i]) + v_off, int(tris[i + 1]) + v_off, int(tris[i + 2]) + v_off
                    lines.append(f"f {a} {b} {c}")
            v_off += len(positions)
    dest.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return dest


def convert_model(path, out, fmt=None):
    src = Path(path)
    dest = Path(out)
    fmt = (fmt or dest.suffix.lstrip(".") or "").lower()
    if fmt.startswith("."):
        fmt = fmt[1:]
    src_ext = src.suffix.lower()

    if src_ext in (".glb", ".gltf") and fmt in ("glb", "gltf"):
        gltf = load_gltf(src)
        if fmt == "glb":
            dest = dest.with_suffix(".glb")
        else:
            dest = dest.with_suffix(".gltf")
        save_gltf(gltf, dest)
        return f"Wrote {dest}"

    if src_ext in (".glb", ".gltf") and fmt == "obj":
        gltf = load_gltf(src)
        dest = dest.with_suffix(".obj")
        _export_obj(gltf, dest)
        return f"Wrote {dest} (geometry only, no rig)"

    blender = find_blender()
    if not blender:
        raise Model3DError(
            f"cannot convert {src_ext} -> .{fmt} without Blender. "
            "Install Blender and ensure `blender` is on PATH, or pass a .glb/.gltf."
        )
    dest.parent.mkdir(parents=True, exist_ok=True)
    script = f"""
import bpy
bpy.ops.wm.read_factory_settings(use_empty=True)
src = r{str(src.resolve())!r}
dst = r{str(dest.resolve())!r}
ext = {src_ext!r}
out_ext = {('.' + fmt) if not fmt.startswith('.') else fmt!r}
if ext == '.fbx':
    bpy.ops.import_scene.fbx(filepath=src)
elif ext == '.obj':
    bpy.ops.wm.obj_import(filepath=src)
elif ext == '.dae':
    bpy.ops.wm.collada_import(filepath=src)
elif ext in ('.glb', '.gltf'):
    bpy.ops.import_scene.gltf(filepath=src)
else:
    raise SystemExit('unsupported import ' + ext)
if out_ext in ('.glb', '.gltf'):
    bpy.ops.export_scene.gltf(filepath=dst, export_format='GLB' if dst.lower().endswith('.glb') else 'GLTF_SEPARATE')
elif out_ext == '.fbx':
    bpy.ops.export_scene.fbx(filepath=dst)
elif out_ext == '.obj':
    bpy.ops.wm.obj_export(filepath=dst)
else:
    raise SystemExit('unsupported export ' + out_ext)
"""
    with tempfile.NamedTemporaryFile("w", suffix=".py", delete=False, encoding="utf-8") as fh:
        fh.write(script)
        script_path = fh.name
    try:
        proc = subprocess.run(
            [blender, "--background", "--python", script_path],
            capture_output=True,
            text=True,
            timeout=180,
        )
    finally:
        try:
            os.unlink(script_path)
        except Exception:
            pass
    if proc.returncode != 0:
        err = (proc.stderr or proc.stdout or "")[-1500:]
        raise Model3DError(f"Blender convert failed:\n{err}")
    if not dest.exists():
        raise Model3DError(f"Blender reported success but {dest} was not created")
    return f"Wrote {dest} via Blender"


def blender_status():
    exe = find_blender()
    if not exe:
        return "Blender not found. glb/gltf still work. Install Blender to convert FBX/OBJ/DAE."
    try:
        proc = subprocess.run([exe, "--version"], capture_output=True, text=True, timeout=20)
        ver = (proc.stdout or proc.stderr or "").splitlines()[0] if proc.returncode == 0 else "found"
        return f"Blender: {exe}\n{ver}"
    except Exception as e:
        return f"Blender at {exe} but --version failed: {e}"


def run_blender_script(script, timeout=180):
    """Run arbitrary Python inside Blender's background mode (bpy is available)
    and return combined stdout/stderr. Unlike convert_model() above (a fixed
    import/export script for one format conversion), this hands the model a
    real scripting surface -- creating/editing meshes, materials, lighting,
    rendering to an image, running Blender's own operators -- anything the
    bpy API exposes, driven by a script the agent writes per-task."""
    blender = find_blender()
    if not blender:
        raise Model3DError(
            "Blender not found. Install Blender and ensure `blender` is on PATH, "
            "or install it at the default location for your OS."
        )
    with tempfile.NamedTemporaryFile("w", suffix=".py", delete=False, encoding="utf-8") as fh:
        fh.write(script)
        script_path = fh.name
    try:
        proc = subprocess.run(
            [blender, "--background", "--python", script_path],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    finally:
        try:
            os.unlink(script_path)
        except Exception:
            pass
    out = (proc.stdout or "").strip()
    err = (proc.stderr or "").strip()
    combined = (out + ("\n[stderr]\n" + err if err else "")).strip()
    if proc.returncode != 0:
        raise Model3DError(f"Blender script failed (exit {proc.returncode}):\n{combined[-1500:]}")
    return combined[-4000:] if combined else "(Blender script ran with no output)"
