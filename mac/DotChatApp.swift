// Dot: a small Mac app that shows Dot's iMessage-style chat (served by Dot at 127.0.0.1:8767/chat).
import Cocoa
import WebKit
import Speech
import AVFoundation

final class AppDelegate: NSObject, NSApplicationDelegate, WKUIDelegate, WKNavigationDelegate, WKScriptMessageHandler {
    let voice = Voice()
    var window: NSWindow!
    var web: WKWebView!

    func applicationDidFinishLaunching(_ n: Notification) {
        let mainMenu = NSMenu()
        let appItem = NSMenuItem(); mainMenu.addItem(appItem)
        let appMenu = NSMenu()
        appMenu.addItem(withTitle: "Quit Dot", action: #selector(NSApplication.terminate(_:)), keyEquivalent: "q")
        appItem.submenu = appMenu
        let editItem = NSMenuItem(); mainMenu.addItem(editItem)
        let edit = NSMenu(title: "Edit")
        edit.addItem(withTitle: "Cut", action: #selector(NSText.cut(_:)), keyEquivalent: "x")
        edit.addItem(withTitle: "Copy", action: #selector(NSText.copy(_:)), keyEquivalent: "c")
        edit.addItem(withTitle: "Paste", action: #selector(NSText.paste(_:)), keyEquivalent: "v")
        edit.addItem(withTitle: "Select All", action: #selector(NSText.selectAll(_:)), keyEquivalent: "a")
        editItem.submenu = edit
        NSApp.mainMenu = mainMenu

        let config = WKWebViewConfiguration()
        config.userContentController.add(self, name: "voice")
        config.userContentController.add(self, name: "screen")
        web = WKWebView(frame: .zero, configuration: config)
        voice.onText = { [weak self] text, done in self?.js("window.dotVoice", [text, done]) }
        voice.onError = { [weak self] msg in self?.js("window.dotVoiceError", [msg]) }
        web.uiDelegate = self
        web.navigationDelegate = self
        window = NSWindow(contentRect: NSRect(x: 0, y: 0, width: 430, height: 760),
                          styleMask: [.titled, .closable, .miniaturizable, .resizable, .fullSizeContentView],
                          backing: .buffered, defer: false)
        window.titlebarAppearsTransparent = true
        window.titleVisibility = .hidden
        window.title = "Dot"
        window.minSize = NSSize(width: 320, height: 420)
        window.contentView = web
        window.setFrameAutosaveName("DotChat")
        if !window.setFrameUsingName("DotChat") { window.center() }
        window.makeKeyAndOrderFront(nil)
        NSApp.activate(ignoringOtherApps: true)
        DispatchQueue.global().async { self.start() }
    }

    func start() {
        let home = FileManager.default.homeDirectoryForCurrentUser
        if !up() {
            let p = Process()
            p.executableURL = URL(fileURLWithPath: "/bin/launchctl")
            p.arguments = ["kickstart", "-k", "gui/\(getuid())/com.period.dot"]
            try? p.run(); p.waitUntilExit()
            for _ in 0..<20 where !up() { Thread.sleep(forTimeInterval: 1) }
        }
        let key = (try? String(contentsOf: home.appendingPathComponent(".period_dots/key"), encoding: .utf8))?
            .trimmingCharacters(in: .whitespacesAndNewlines) ?? ""
        DispatchQueue.main.async {
            if key.isEmpty || !self.up() {
                self.web.loadHTMLString("<body style='font:15px -apple-system;padding:40px;text-align:center;color:#888'>Dot isn't running.<br><br>To check it, open Terminal and run:<br><code>cd ~/Period && .venv/bin/python pd_dots.py doctor</code></body>", baseURL: nil)
            } else {
                self.web.load(URLRequest(url: URL(string: "http://127.0.0.1:8767/chat?k=\(key)")!))
            }
        }
    }

    func up() -> Bool {
        var ok = false
        let sem = DispatchSemaphore(value: 0)
        var req = URLRequest(url: URL(string: "http://127.0.0.1:8767/")!); req.timeoutInterval = 2
        URLSession.shared.dataTask(with: req) { _, r, _ in ok = r != nil; sem.signal() }.resume()
        sem.wait()
        return ok
    }

    // Links and the "watch Dot's computer" button open in the normal browser.
    func webView(_ w: WKWebView, createWebViewWith c: WKWebViewConfiguration, for a: WKNavigationAction,
                 windowFeatures f: WKWindowFeatures) -> WKWebView? {
        let popup = WKWebView(frame: .zero, configuration: c)
        popup.navigationDelegate = self
        popups.append(popup)
        return popup
    }
    var popups: [WKWebView] = []
    func webView(_ w: WKWebView, decidePolicyFor a: WKNavigationAction, decisionHandler: @escaping (WKNavigationActionPolicy) -> Void) {
        if w === screenWeb { return decisionHandler(.allow) }
        if w !== web, let u = a.request.url, u.scheme?.hasPrefix("http") == true {
            NSWorkspace.shared.open(u)
            popups.removeAll { $0 === w }
            return decisionHandler(.cancel)
        }
        if w === web, a.navigationType == .linkActivated, let u = a.request.url {
            NSWorkspace.shared.open(u)
            return decisionHandler(.cancel)
        }
        decisionHandler(.allow)
    }

    func userContentController(_ c: WKUserContentController, didReceive m: WKScriptMessage) {
        if m.name == "screen" {
            if let s = m.body as? String, let u = URL(string: s) { showScreen(u) }
            return
        }
        if (m.body as? String) == "start" { voice.start() } else { voice.stop() }
    }

    // Dot's own computer, live, in a window of this app, with a plain explanation on top.
    var screenWindow: NSWindow?
    var screenWeb: WKWebView?
    func showScreen(_ url: URL) {
        if let w = screenWindow, let v = screenWeb {
            v.load(URLRequest(url: url)); w.makeKeyAndOrderFront(nil); return
        }
        let note = NSTextField(wrappingLabelWithString:
            "This is Dot's own computer. It lives inside your Mac but is separate from your stuff. " +
            "You're watching it work live.\n" +
            "You can click and type in here to help it, for example to sign in to a website. " +
            "Closing this window doesn't stop Dot.")
        note.font = .systemFont(ofSize: 13)
        note.textColor = .secondaryLabelColor
        let v = WKWebView(frame: .zero, configuration: WKWebViewConfiguration())
        v.navigationDelegate = self
        let stack = NSStackView(views: [note, v])
        stack.orientation = .vertical
        stack.alignment = .leading
        stack.spacing = 8
        stack.edgeInsets = NSEdgeInsets(top: 10, left: 14, bottom: 0, right: 14)
        v.translatesAutoresizingMaskIntoConstraints = false
        NSLayoutConstraint.activate([
            v.leadingAnchor.constraint(equalTo: stack.leadingAnchor),
            v.trailingAnchor.constraint(equalTo: stack.trailingAnchor),
            note.trailingAnchor.constraint(equalTo: stack.trailingAnchor, constant: -14),
        ])
        let w = NSWindow(contentRect: NSRect(x: 0, y: 0, width: 1100, height: 760),
                         styleMask: [.titled, .closable, .miniaturizable, .resizable], backing: .buffered, defer: false)
        w.title = "Dot's computer"
        w.contentView = stack
        w.isReleasedWhenClosed = false
        w.setFrameAutosaveName("DotScreen")
        if !w.setFrameUsingName("DotScreen") { w.center() }
        screenWindow = w; screenWeb = v
        v.load(URLRequest(url: url))
        w.makeKeyAndOrderFront(nil)
    }

    func js(_ fn: String, _ args: [Any]) {
        guard let data = try? JSONSerialization.data(withJSONObject: args),
              let list = String(data: data, encoding: .utf8) else { return }
        DispatchQueue.main.async { self.web.evaluateJavaScript("\(fn).apply(null, \(list))") }
    }

    func applicationShouldTerminateAfterLastWindowClosed(_ s: NSApplication) -> Bool { true }
    func applicationShouldHandleReopen(_ s: NSApplication, hasVisibleWindows f: Bool) -> Bool { window.makeKeyAndOrderFront(nil); return true }
}

let app = NSApplication.shared
let delegate = AppDelegate()
app.delegate = delegate
app.setActivationPolicy(.regular)
app.run()

// Speech to text with Apple's recognizer (on this Mac when it can). Only listens while the mic button is on.
final class Voice {
    var onText: (String, Bool) -> Void = { _, _ in }
    var onError: (String) -> Void = { _ in }
    private let engine = AVAudioEngine()
    private var request: SFSpeechAudioBufferRecognitionRequest?
    private var task: SFSpeechRecognitionTask?
    private let recognizer = SFSpeechRecognizer(locale: Locale(identifier: "en-US"))

    func start() {
        SFSpeechRecognizer.requestAuthorization { status in
            guard status == .authorized else {
                return self.onError("Turn on Speech Recognition for Dot in System Settings > Privacy & Security")
            }
            AVCaptureDevice.requestAccess(for: .audio) { ok in
                DispatchQueue.main.async {
                    ok ? self.begin() : self.onError("Turn on the Microphone for Dot in System Settings > Privacy & Security")
                }
            }
        }
    }

    private func begin() {
        stop()
        guard let recognizer = recognizer, recognizer.isAvailable else { return onError("Speech recognition isn't available right now") }
        let req = SFSpeechAudioBufferRecognitionRequest()
        req.shouldReportPartialResults = true
        if recognizer.supportsOnDeviceRecognition { req.requiresOnDeviceRecognition = true }
        request = req
        let input = engine.inputNode
        input.installTap(onBus: 0, bufferSize: 1024, format: input.outputFormat(forBus: 0)) { buf, _ in req.append(buf) }
        engine.prepare()
        do { try engine.start() } catch { input.removeTap(onBus: 0); return onError("Couldn't use the microphone") }
        task = recognizer.recognitionTask(with: req) { [weak self] result, error in
            DispatchQueue.main.async {
                guard let self = self else { return }
                let current = self.request === req || self.request == nil
                guard current else { return }  // a late answer from an earlier recording
                if let r = result {
                    self.onText(r.bestTranscription.formattedString, r.isFinal)
                    if r.isFinal && self.request === req { self.stop() }
                } else if error != nil {
                    self.onText("", true)
                    if self.request === req { self.stop() }
                }
            }
        }
    }

    func stop() {
        if engine.isRunning { engine.stop(); engine.inputNode.removeTap(onBus: 0) }
        request?.endAudio(); request = nil
        task?.finish(); task = nil
    }
}
