#!/usr/bin/env python3
"""List every production construction site of messages of enum MSG (i.e. every place that can put a MSG into
a mailbox), plus every StageRef<MSG> / contramap path, at a given commit. Read-only (git grep on the commit).

usage: producers.py REPO COMMIT MSG   e.g. producers.py /workspace/amaru-research/repo 33d62a6f ManagerMessage
Construction = `MSG::Variant` not followed by `=>` on the same line (match arms are consumers), outside tests.
"""
import re, subprocess, sys, collections
repo, commit, msg = sys.argv[1:4]
def grep(pat):
    r = subprocess.run(["git","-C",repo,"grep","-n","-E",pat,commit,"--","crates/*.rs"],capture_output=True,text=True)
    return [l.split(":",3)[1:] for l in r.stdout.splitlines()]
TEST = re.compile(r"(/tests?/|tests?\.rs$|_tests?\.rs$|/examples/|/benches/|simulation|test_)")
def in_test_mod(path, line):
    # crude: treat anything after a `#[cfg(test)]` line in the file as test code
    src = subprocess.run(["git","-C",repo,"show",f"{commit}:{path}"],capture_output=True,text=True).stdout.splitlines()
    lines = src[:int(line)]
    for i,l in enumerate(lines):
        if l.strip().startswith("#[cfg(test)]"):
            nxt = next((x.strip() for x in src[i+1:i+3] if x.strip()), "")
            if re.match(r"(pub(\(crate\))?\s+)?mod\s+\w+\s*\{", nxt):
                return True  # inline `#[cfg(test)] mod tests { ... }`: everything after is test code
            # `mod x;` (external file) or an item-level cfg(test): not a region (over-inclusion is conservative)
    return False
sites = collections.defaultdict(list)
for path, line, text in grep(rf"\b{msg}::[A-Z][A-Za-z]*"):
    if TEST.search(path) or in_test_mod(path, line): continue
    if text.lstrip().startswith("//"): continue
    for v in re.findall(rf"\b{msg}::([A-Z][A-Za-z]*)", text):
        after = text.split(f"{msg}::{v}",1)[1]
        if "=>" in after.split(";")[0] and not re.search(r"\bsend\b|preload|::new\(", text): continue  # match arm
        if re.match(r"\s*(\(|\{|\s*$|,)", after) is None and not after.startswith(")"): pass
        sites[v].append(f"{path}:{line}: {text.strip()[:110]}")
print(f"# Producers of {msg} at {commit}\n")
for v in sorted(sites):
    print(f"## {v}")
    for s in sites[v]: print("  " + s)
print("\n# StageRef / contramap paths")
for path, line, text in grep(rf"StageRef<{msg}>|contramap.*{msg}|{msg}.*contramap"):
    if TEST.search(path) or in_test_mod(path, line): continue
    print(f"  {path}:{line}: {text.strip()[:110]}")
