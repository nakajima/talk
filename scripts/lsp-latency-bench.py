#!/usr/bin/env python3
import argparse
import json
import math
import os
from pathlib import Path
import platform
import select
import subprocess
import sys
import tempfile
import time
from urllib.parse import quote


class LspClient:
    def __init__(self, binary, root, source):
        self.root = root.resolve()
        self.source = source.resolve()
        self.text = self.source.read_text()
        self.uri = self.file_uri(self.source)
        self.version = 1
        self.modified = False
        self.next_id = 1
        self.buffer = b""
        self.refresh_count = 0
        self.stderr_file = tempfile.TemporaryFile()
        self.log_directory = tempfile.TemporaryDirectory(prefix="talk-lsp-bench-")
        self.process = subprocess.Popen(
            [str(binary.resolve()), "lsp", "--stdio"],
            cwd=self.log_directory.name,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=self.stderr_file,
        )

    @staticmethod
    def file_uri(path):
        return "file://" + quote(str(path))

    def send(self, payload):
        body = json.dumps(payload, separators=(",", ":")).encode()
        message = f"Content-Length: {len(body)}\r\n\r\n".encode() + body
        self.process.stdin.write(message)
        self.process.stdin.flush()

    def notify(self, method, params):
        self.send({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method, params):
        request_id = self.next_id
        self.next_id += 1
        self.send(
            {
                "jsonrpc": "2.0",
                "id": request_id,
                "method": method,
                "params": params,
            }
        )
        return request_id

    def receive(self, timeout):
        deadline = time.monotonic() + timeout
        while True:
            header_end = self.buffer.find(b"\r\n\r\n")
            if header_end >= 0:
                content_length = None
                headers = self.buffer[:header_end].decode()
                for line in headers.split("\r\n"):
                    if line.lower().startswith("content-length:"):
                        content_length = int(line.split(":", 1)[1])
                        break
                if content_length is None:
                    raise RuntimeError("LSP response omitted Content-Length")
                message_end = header_end + 4 + content_length
                if len(self.buffer) >= message_end:
                    body = self.buffer[header_end + 4 : message_end]
                    self.buffer = self.buffer[message_end:]
                    return json.loads(body)

            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("timed out waiting for LSP message")
            ready, _, _ = select.select([self.process.stdout], [], [], remaining)
            if not ready:
                raise TimeoutError("timed out waiting for LSP message")
            chunk = os.read(self.process.stdout.fileno(), 65536)
            if not chunk:
                self.stderr_file.seek(0)
                stderr = self.stderr_file.read().decode(errors="replace")
                raise RuntimeError(f"LSP server exited early: {stderr}")
            self.buffer += chunk

    def handle_auxiliary(self, message):
        if "id" in message and "method" in message:
            if message["method"] == "workspace/semanticTokens/refresh":
                self.refresh_count += 1
            self.send({"jsonrpc": "2.0", "id": message["id"], "result": None})
            return True
        return False

    def wait_response(self, request_id, timeout):
        deadline = time.monotonic() + timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(f"timed out waiting for response {request_id}")
            message = self.receive(remaining)
            if message.get("id") == request_id and "method" not in message:
                return message
            self.handle_auxiliary(message)

    def timed_request(self, method, params, timeout):
        started = time.monotonic_ns()
        request_id = self.request(method, params)
        self.wait_response(request_id, timeout)
        return (time.monotonic_ns() - started) / 1_000_000.0

    def wait_for_refresh(self, previous_count, timeout):
        deadline = time.monotonic() + timeout
        while self.refresh_count <= previous_count:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("timed out waiting for semantic token refresh")
            message = self.receive(remaining)
            self.handle_auxiliary(message)

    def initialize(self, timeout):
        request_id = self.request(
            "initialize",
            {
                "processId": os.getpid(),
                "rootUri": self.file_uri(self.root),
                "workspaceFolders": [
                    {"uri": self.file_uri(self.root), "name": self.root.name}
                ],
                "capabilities": {
                    "workspace": {"semanticTokens": {"refreshSupport": True}}
                },
            },
        )
        self.wait_response(request_id, timeout)
        self.notify("initialized", {})
        refresh_count = self.refresh_count
        self.notify(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": self.uri,
                    "languageId": "talk",
                    "version": self.version,
                    "text": self.text,
                }
            },
        )
        self.wait_for_refresh(refresh_count, timeout)

    def change(self):
        self.version += 1
        self.modified = not self.modified
        text = self.text + (" " if self.modified else "")
        self.notify(
            "textDocument/didChange",
            {
                "textDocument": {"uri": self.uri, "version": self.version},
                "contentChanges": [{"text": text}],
            },
        )

    def edited_request(self, method, timeout):
        refresh_count = self.refresh_count
        self.change()
        elapsed = self.timed_request(
            method,
            {"textDocument": {"uri": self.uri}, "position": {"line": 0, "character": 0}},
            timeout,
        )
        self.wait_for_refresh(refresh_count, timeout)
        return elapsed

    def edited_refresh(self, timeout):
        refresh_count = self.refresh_count
        started = time.monotonic_ns()
        self.change()
        self.wait_for_refresh(refresh_count, timeout)
        return (time.monotonic_ns() - started) / 1_000_000.0

    def close(self, timeout):
        if self.process.poll() is None:
            try:
                request_id = self.request("shutdown", None)
                self.wait_response(request_id, min(timeout, 5.0))
                self.notify("exit", None)
                self.process.wait(timeout=2)
            except Exception:
                self.process.terminate()
                try:
                    self.process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    self.process.kill()
        self.stderr_file.close()
        self.log_directory.cleanup()


class Benchmark:
    def __init__(self, arguments, root):
        self.arguments = arguments
        self.root = root

    def cases(self):
        definitions = {
            "small": (
                self.root / "benches/editor/fixtures",
                self.root / "benches/editor/fixtures/small.tlk",
            ),
            "core": (self.root / "core", self.root / "core/Array.tlk"),
            "syntax": (
                self.root / "stdlib/syntax",
                self.root / "stdlib/syntax/Parser.tlk",
            ),
        }
        for name in self.arguments.case:
            if name not in definitions:
                raise ValueError(f"unknown case {name!r}; expected small, core, or syntax")
            workspace, source = definitions[name]
            yield name, workspace, source

    def measure(self, client, case_name, operation_name, operation):
        print(f"warming {case_name} {operation_name}", file=sys.stderr)
        for _ in range(self.arguments.warmups):
            operation()

        samples = []
        for index in range(self.arguments.iterations):
            print(
                f"measuring {case_name} {operation_name} "
                f"{index + 1}/{self.arguments.iterations}",
                file=sys.stderr,
            )
            samples.append(operation())

        ordered = sorted(samples)
        median = ordered[len(ordered) // 2]
        p95 = ordered[max(0, math.ceil(len(ordered) * 0.95) - 1)]
        print(
            json.dumps(
                {
                    "type": "result",
                    "case": case_name,
                    "operation": operation_name,
                    "focus": str(client.source),
                    "focus_bytes": len(client.text.encode()),
                    "workspace": str(client.root),
                    "warmups": self.arguments.warmups,
                    "iterations": self.arguments.iterations,
                    "median_ms": round(median, 3),
                    "p95_ms": round(p95, 3),
                    "samples_ms": [round(sample, 3) for sample in samples],
                },
                separators=(",", ":"),
            )
        )

    def run_case(self, name, workspace, source):
        client = LspClient(self.arguments.binary, workspace, source)
        try:
            print(f"initializing {name}", file=sys.stderr)
            client.initialize(self.arguments.timeout)
            self.measure(
                client,
                name,
                "completion_after_edit",
                lambda: client.edited_request(
                    "textDocument/completion", self.arguments.timeout
                ),
            )
            self.measure(
                client,
                name,
                "definition_after_edit",
                lambda: client.edited_request(
                    "textDocument/definition", self.arguments.timeout
                ),
            )
            self.measure(
                client,
                name,
                "semantic_refresh_after_edit",
                lambda: client.edited_refresh(self.arguments.timeout),
            )
        finally:
            client.close(self.arguments.timeout)

    def run(self):
        for name, workspace, source in self.cases():
            self.run_case(name, workspace, source)


def git_output(root, *arguments):
    result = subprocess.run(
        ["git", *arguments],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        check=False,
    )
    return result.stdout.strip() if result.returncode == 0 else "unknown"


def parse_arguments(root):
    parser = argparse.ArgumentParser(
        description="Measure Talk LSP latency after a semantically neutral edit."
    )
    parser.add_argument(
        "--binary",
        type=Path,
        default=root / "target/release/talk",
        help="talk executable to benchmark",
    )
    parser.add_argument(
        "--case",
        action="append",
        choices=["small", "core", "syntax"],
        help="case to run; may be repeated; defaults to all cases",
    )
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--iterations", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=120.0)
    arguments = parser.parse_args()
    if arguments.case is None:
        arguments.case = ["small", "core", "syntax"]
    if arguments.warmups < 0:
        parser.error("--warmups must be non-negative")
    if arguments.iterations <= 0:
        parser.error("--iterations must be greater than zero")
    if arguments.timeout <= 0:
        parser.error("--timeout must be greater than zero")
    if not arguments.binary.is_file():
        parser.error(
            f"{arguments.binary} does not exist; run cargo build --release --bin talk"
        )
    return arguments


def main():
    root = Path(__file__).resolve().parent.parent
    arguments = parse_arguments(root)
    binary = arguments.binary.resolve()
    metadata = {
        "type": "metadata",
        "format": 1,
        "benchmark": "lsp_latency",
        "commit": git_output(root, "rev-parse", "HEAD"),
        "worktree_dirty": bool(git_output(root, "status", "--porcelain")),
        "generated_at_unix": int(time.time()),
        "os": platform.system(),
        "arch": platform.machine(),
        "python": platform.python_version(),
        "binary": str(binary),
        "binary_bytes": binary.stat().st_size,
    }
    print(json.dumps(metadata, separators=(",", ":")))
    Benchmark(arguments, root).run()


if __name__ == "__main__":
    main()
