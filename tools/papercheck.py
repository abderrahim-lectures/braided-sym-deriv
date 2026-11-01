#!/usr/bin/env python3
"""Mechanical gate for the paper-plus-Lean review. Exit 0 iff everything passes.

Usage: python3 tools/papercheck.py [--skip-pdf] [--skip-lean]

Legs (each pass prints which legs ran, so a PASS always says what it checked):

PDF:
  1. Force a latexmk rebuild (`-g`): 0 overfull, 0 undefined refs/citations, 0 TeX errors.
  2. The fresh build's page count must equal the released artifact's page count, and the
     fresh build's text must equal the released artifact's text (pdftotext, modulo the
     "compiled <date>" line). The released artifact is pdf/braided-sym-deriv-<v>.pdf with
     <v> = \\paperversion; a missing or differing artifact fails.
  3. The released artifact's page-1 label must print \\paperversion (catches a stale release).

Lean:
  1. lean/lake-manifest.json must exist (reproducibility precondition) and the toolchain
     on PATH must be the one lean/lean-toolchain pins.
  2. `lake build` of the default target: hash-based dependency tracking replaces the old
     mtime/stale-olean logic; there are no hand-managed oleans to go stale.
  3. Axiom audit (`lake env lean check_axioms.lean`): every declaration's footprint must be
     inside {propext, Classical.choice, Quot.sound} plus the explicitly whitelisted
     native_decide compiler-trust axioms (enumerated below); sorryAx or any other axiom
     fails. The whitelist is data, not a guess.
  4. Source trust scan: occurrences of sorry / native_decide / axiom declarations in
     lean/Research are counted against a waiver list; new occurrences fail.

Diagnostics: the tail of a failing command's output is printed; a process killed by a
signal or by the timeout is reported as UNKNOWN (the gate cannot pass on it, but the
message says what happened instead of masquerading as a compile error).
"""
import argparse, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
fails, notes = [], []

# --- data: the enumerated trust whitelist --------------------------------------
# The five known native_decide tactic uses.  A theorem proved `by native_decide`
# depends on the compiler-trust axiom `<name>._native.native_decide.ax_1_1`; the
# three anonymous `example`s cannot be named by #print axioms at all, so all five
# are whitelisted by file and line here and counted in the audit leg.
NATIVE_DECIDE_SITES = [
    "lean/Research/BraidedSymDeriv/Triangular.lean:132",
    "lean/Research/BraidedSymDeriv/Triangular.lean:166",
    "lean/Research/BraidedSymDeriv/Counterexamples.lean:158",
    "lean/Research/BraidedSymDeriv/Counterexamples.lean:386",
    "lean/Research/BraidedSymDeriv/Counterexamples.lean:419",
]
OK_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def strip_lean_comments(text):
    """Remove block comments (/- ... -/, nested) and line comments (-- ...)."""
    out, i, n = [], 0, len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("/-", i):
            depth, i = 1, i + 2
        elif depth > 0 and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth > 0 and text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth == 0 and text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        else:
            if depth == 0:
                out.append(text[i])
            elif text[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)

def run(cmd, cwd, timeout=3600):
    """Run; report kills/timeouts as None (UNKNOWN) rather than plain failures."""
    try:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None

def tail(out, n=15):
    lines = [l for l in out.splitlines() if l.strip()]
    return "\n".join(lines[-n:])

def failed(what, r=None):
    if r is None:
        fails.append("%s: UNKNOWN (killed or timed out; not a compile verdict)" % what)
        return
    msg = "%s (rc=%d)" % (what, r.returncode)
    if r.stdout or r.stderr:
        msg += "\n    " + tail(r.stdout + "\n" + r.stderr).replace("\n", "\n    ")
    fails.append(msg)

# --- PDF leg -------------------------------------------------------------------
def check_pdf():
    paper = os.path.join(ROOT, "paper")
    src = open(os.path.join(paper, "braided-sym-deriv.tex")).read()
    ver = re.search(r"\\newcommand\{\\paperversion\}\{(\d+)\}", src)
    if not ver:
        fails.append("cannot read \\paperversion from the source"); return
    v = ver.group(1)
    m = re.search(r"\$jobname\s*=\s*'([^']+)'", open(os.path.join(paper, "latexmkrc")).read())
    job = m.group(1) if m else "paper"
    r = run(["latexmk", "-g", "-pdf", "-interaction=nonstopmode", "braided-sym-deriv.tex"], paper)
    if r is None or r.returncode != 0:
        failed("latexmk rebuild", r); return
    log = os.path.join(paper, "build", job + ".log")
    pdf = os.path.join(paper, "build", job + ".pdf")
    if not (os.path.exists(log) and os.path.exists(pdf)):
        fails.append("build artefacts missing (%s)" % job); return
    logtext = open(log, errors="ignore").read()
    over = logtext.count("Overfull")
    undef = [l for l in logtext.splitlines() if "undefined" in l.lower()]
    errors = [l for l in logtext.splitlines() if l.startswith("! ")]
    released = os.path.join(ROOT, "pdf", "braided-sym-deriv-v%s.pdf" % v)
    if not os.path.exists(released):
        fails.append("released artefact pdf/braided-sym-deriv-v%s.pdf is missing" % v); return
    try:
        fresh_txt = subprocess.run(["pdftotext", "-q", pdf, "-"], capture_output=True, text=True, check=True).stdout
        rel_txt = subprocess.run(["pdftotext", "-q", released, "-"], capture_output=True, text=True, check=True).stdout
        fresh_info = subprocess.run(["pdfinfo", pdf], capture_output=True, text=True, check=True).stdout
        rel_info = subprocess.run(["pdfinfo", released], capture_output=True, text=True, check=True).stdout
        rel_label = subprocess.run(["pdftotext", "-q", "-f", "1", "-l", "1", released, "-"],
                                  capture_output=True, text=True, check=True).stdout
    except Exception as e:
        fails.append("pdf tooling unavailable: %s" % e); return
    norm = lambda t: re.sub(r"compiled \d{4}/\d{2}/\d{2}", "compiled <DATE>", t)
    fresh_pages = re.search(r"Pages:\s+(\d+)", fresh_info)
    rel_pages = re.search(r"Pages:\s+(\d+)", rel_info)
    same_text = norm(fresh_txt) == norm(rel_txt)
    same_pages = fresh_pages and rel_pages and fresh_pages.group(1) == rel_pages.group(1)
    ok_label = ("version %s," % v) in rel_label
    notes.append("pdf: fresh %s pp vs released %s pp, %d overfull, %d undefined, "
                  "text %s, released label %s" % (
        fresh_pages.group(1) if fresh_pages else "?", rel_pages.group(1) if rel_pages else "?",
        over, len(undef), "identical" if same_text else "DIFFERS",
        "ok" if ok_label else "MISMATCH"))
    if over: fails.append("%d overfull boxes" % over)
    if undef: fails.append("LaTeX: %d undefined reference/citation warning(s)" % len(undef))
    if errors: fails.append("LaTeX errors in the log: %d" % len(errors))
    if not same_pages: fails.append("page count: fresh build %s vs released %s" % (
        fresh_pages.group(1) if fresh_pages else "?", rel_pages.group(1) if rel_pages else "?"))
    if not same_text: fails.append("fresh build text differs from the released artefact "
                                   "(stale source or stale release)")
    if not ok_label: fails.append("released artefact does not print version %s on page 1" % v)

# --- Lean leg ------------------------------------------------------------------
def check_lean():
    lean = os.path.join(ROOT, "lean")
    manifest = os.path.join(lean, "lake-manifest.json")
    if not os.path.exists(manifest):
        fails.append("lean/lake-manifest.json is missing: lake build would resolve an "
                     "unpinned Mathlib; run `lake update` and commit the manifest")
        return
    pin = open(os.path.join(lean, "lean-toolchain")).read().strip()
    pin_ver = pin.split(":")[-1].lstrip("v")
    r = run(["lean", "--version"], lean)
    if r is None or r.returncode != 0:
        failed("lean --version", r); return
    if pin_ver not in r.stdout:
        fails.append("toolchain mismatch: lean-toolchain pins %s but `lean` reports %s" % (
            pin, r.stdout.strip()))
        return
    r = run(["lake", "build"], lean)
    if r is None or r.returncode != 0:
        failed("lake build", r); return
    built = len([l for l in (r.stdout or "").splitlines() if "Built" in l or "Rebuilt" in l])
    notes.append("lean: lake build green (%d module(s) built this run)" % built)

    # axiom audit
    r = run(["lake", "env", "lean", "check_axioms.lean"], lean)
    if r is None or r.returncode != 0:
        failed("axiom audit (check_axioms.lean)", r); return
    text = r.stdout or ""
    # footprints may wrap across lines; match to the closing bracket
    footprints = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
    bad, ok, native = [], 0, 0
    for name, ax_s in footprints:
        axioms = [a.strip() for a in ax_s.replace("\n", " ").split(",") if a.strip()]
        native_here = [a for a in axioms if "_native.native_decide.ax_1_1" in a]
        native += len(native_here)
        bad_here = [a for a in axioms
                    if a not in OK_AXIOMS and "_native.native_decide.ax_1_1" not in a]
        if bad_here:
            bad.append("%s: %s" % (name, ", ".join(bad_here)))
        else:
            ok += 1
    notes.append("axiom audit: %d declarations, %d whitelisted native_decide "
                 "footprint(s)" % (ok, native))
    if bad:
        fails.append("axiom audit: non-whitelisted axioms: " + "; ".join(bad[:10])
                     + (" ... (%d total)" % len(bad) if len(bad) > 10 else ""))
    if native > len(NATIVE_DECIDE_SITES):
        fails.append("axiom audit: %d native_decide footprints but only %d whitelisted sites"
                     % (native, len(NATIVE_DECIDE_SITES)))

    # source trust scan (comments stripped, so only real uses count)
    findings = []
    for sub in ("Research", "Background"):
      d = os.path.join(lean, sub)
      if not os.path.isdir(d): continue
      for dirpath, _dirs, files in os.walk(d):
        for f in sorted(files):
            if not f.endswith(".lean"): continue
            path = os.path.join(dirpath, f)
            rel = os.path.relpath(path, ROOT)
            code = strip_lean_comments(open(path, errors="ignore").read())
            for i, line in enumerate(code.splitlines(), 1):
                if re.search(r"\bsorry\b", line) or re.search(r"\bnative_decide\b", line) \
                   or re.match(r"\s*axiom\b", line):
                    findings.append("%s:%d" % (rel, i))
    fresh = [s for s in findings if s not in NATIVE_DECIDE_SITES]
    notes.append("trust scan: %d sorry/native_decide/axiom use(s) outside comments, "
                 "%d whitelisted, %d new" % (len(findings), len(findings) - len(fresh),
                                            len(fresh)))
    if fresh:
        fails.append("trust scan: new sorry/native_decide/axiom use(s): " + ", ".join(fresh[:10]))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--skip-pdf", action="store_true")
    ap.add_argument("--skip-lean", action="store_true")
    a = ap.parse_args()
    if a.skip_pdf and a.skip_lean:
        fails.append("nothing checked (both stages skipped)")
    legs = []
    if not a.skip_pdf:
        legs.append("pdf"); check_pdf()
    if not a.skip_lean:
        legs.append("lean (lake build + axiom audit + trust scan)"); check_lean()
    if legs:
        notes.insert(0, "legs run: " + ", ".join(legs))
    for n in notes: print("note  " + n)
    for f in fails: print("FAIL  " + f)
    print("GATE: " + ("PASS" if not fails else "FAIL"))
    return 0 if not fails else 1

if __name__ == "__main__":
    sys.exit(main())
