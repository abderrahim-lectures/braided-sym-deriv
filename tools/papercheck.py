#!/usr/bin/env python3
"""Mechanical gate for the paper-plus-Lean review. Exit 0 iff everything passes.

Usage: python3 tools/papercheck.py [--skip-pdf] [--skip-lean]
"""
import argparse, os, re, shutil, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
fails, notes = [], []

def run(cmd, cwd, timeout=900, env=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=env)

def check_pdf():
    paper = os.path.join(ROOT, "paper")
    m = re.search(r"\$jobname\s*=\s*'([^']+)'", open(os.path.join(paper, "latexmkrc")).read())
    job = m.group(1) if m else "paper"
    r = run(["latexmk", "-pdf", "-interaction=nonstopmode", "braided-sym-deriv.tex"], paper)
    if r.returncode != 0:
        fails.append("latexmk failed"); return
    log = os.path.join(paper, "build", job + ".log")
    pdf = os.path.join(paper, "build", job + ".pdf")
    if not (os.path.exists(log) and os.path.exists(pdf)):
        fails.append("build artefacts missing (%s)" % job); return
    over = open(log, errors="ignore").read().count("Overfull")
    ver = re.search(r"\\newcommand\{\\paperversion\}\{(\d+)\}", open(os.path.join(paper, "braided-sym-deriv.tex")).read())
    label = subprocess.run(["pdftotext", "-f", "1", "-l", "1", pdf, "-"], capture_output=True, text=True).stdout
    pages = re.search(r"Pages:\s+(\d+)", subprocess.run(["pdfinfo", pdf], capture_output=True, text=True).stdout)
    ok_label = ver and ("version %s" % ver.group(1)) in label
    notes.append("pdf: %s pages, %d overfull, version label %s" % (pages.group(1) if pages else "?", over, "ok" if ok_label else "MISMATCH"))
    if over: fails.append("%d overfull boxes" % over)
    if not ok_label: fails.append("version label does not match \\paperversion")

def check_lean():
    lean = os.path.join(ROOT, "lean")
    env = dict(os.environ); env["LEAN_PATH"] = lean + ":" + env.get("LEAN_PATH", "")
    files = sorted(f for f in os.listdir(os.path.join(lean, "Research/BraidedSymDeriv")) if f.endswith(".lean"))
    bad = []
    for f in files:
        path = os.path.join("Research/BraidedSymDeriv", f)
        r = run(["lean", path], lean, timeout=1800, env=env)
        if r.returncode != 0:
            bad.append(f)
        elif "sorry" in r.stdout or "declaration uses 'sorry'" in r.stdout:
            bad.append(f + " (sorry)")
    notes.append("lean: %d/%d files elaborate" % (len(files) - len(bad), len(files)))
    if bad: fails.append("lean failures: " + ", ".join(bad))
    g = run(["grep", "-rn", "sorry\\|native_decide\\|^axiom", "Research"], lean)
    hits = [l for l in g.stdout.splitlines() if l.strip()]
    if hits:
        notes.append("trust: %d lines mention sorry/native_decide/axiom (review by hand)" % len(hits))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-pdf", action="store_true")
    ap.add_argument("--skip-lean", action="store_true")
    a = ap.parse_args()
    if not a.skip_pdf: check_pdf()
    if not a.skip_lean: check_lean()
    for n in notes: print("note  " + n)
    for f in fails: print("FAIL  " + f)
    print("GATE: " + ("PASS" if not fails else "FAIL"))
    return 0 if not fails else 1

if __name__ == "__main__":
    sys.exit(main())
