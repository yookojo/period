"""Not part of this copy of Dot: pd_remote_memory is one of the original owner's personal add-ons.

Every name here is a harmless no-op (falsy, callable, returns itself), so code that imports it still loads;
pd_dots.owner_extras() keeps the add-on switched off anyway.
"""


class _Nothing:
    def __call__(self, *a, **k):
        return None

    def __getattr__(self, name):
        return self

    def __truediv__(self, other):
        return self

    def __bool__(self):
        return False

    def __iter__(self):
        return iter(())

    def __str__(self):
        return ""

    def exists(self):
        return False


_NOTHING = _Nothing()


def __getattr__(name):
    if name.startswith("__"):
        raise AttributeError(name)
    return _NOTHING
