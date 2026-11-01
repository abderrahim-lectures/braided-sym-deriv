#!/usr/bin/env python3
"""Minimal MCP stdio server exposing one tool: papercheck."""
import json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def gate(args):
    r = subprocess.run([sys.executable, os.path.join(ROOT, "tools", "papercheck.py")] + args,
                       capture_output=True, text=True, timeout=3600, cwd=ROOT)
    return (r.stdout + r.stderr).strip(), r.returncode

for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    try:
        msg = json.loads(line)
    except Exception:
        continue
    rid, method = msg.get("id"), msg.get("method")
    if method == "initialize":
        out = {"jsonrpc": "2.0", "id": rid, "result": {
            "protocolVersion": msg.get("params", {}).get("protocolVersion", "2024-11-05"),
            "capabilities": {"tools": {}}, "serverInfo": {"name": "papercheck", "version": "1"}}}
    elif method == "notifications/initialized":
        continue
    elif method == "tools/list":
        out = {"jsonrpc": "2.0", "id": rid, "result": {"tools": [{
            "name": "papercheck",
            "description": "Run the paper-plus-Lean gate: latexmk, page count, overfull boxes, version label, lean on every file, sorry/native_decide audit. Returns PASS/FAIL.",
            "inputSchema": {"type": "object", "properties": {
                "skip_pdf": {"type": "boolean"}, "skip_lean": {"type": "boolean"}}, "required": []}}]}}
    elif method == "tools/call":
        a = []
        args = msg.get("params", {}).get("arguments", {}) or {}
        if args.get("skip_pdf"): a.append("--skip-pdf")
        if args.get("skip_lean"): a.append("--skip-lean")
        text, code = gate(a)
        out = {"jsonrpc": "2.0", "id": rid, "result": {"content": [{"type": "text", "text": text}], "isError": code != 0}}
    else:
        out = {"jsonrpc": "2.0", "id": rid, "result": {}}
    sys.stdout.write(json.dumps(out) + "\n"); sys.stdout.flush()
