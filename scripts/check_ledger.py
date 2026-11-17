#!/usr/bin/env python3
"""Check that the README assumption ledger is in sync with the Lean sources (ROADMAP M0.3).

Checks:
1. Every module in HolographicUniverse/ is imported by HolographicUniverse.lean and Audit.lean,
   and has a row in the README layout table.
2. Every Lean name cited in backticks in README.md, docs/NOTE.md and docs/ROADMAP.md that looks
   like a declaration name exists in the sources.
3. Every field of `BraneCosmology` is cited in README.md.

Exit status 1 if a check fails. Run from the repository root: python3 scripts/check_ledger.py
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "HolographicUniverse"
DOCS = [ROOT / "README.md", ROOT / "docs" / "NOTE.md", ROOT / "docs" / "ROADMAP.md"]

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|instance)\s+([^\s(:{\[]+)",
    re.M)
NS = re.compile(r"^\s*namespace\s+(\S+)", re.M)


# Names from Lean core, and tactics, that the docs cite.
EXTERNAL = {"Classical.choice", "Quot.sound", "propext", "norm_num"}
MATHLIB = ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"


def in_mathlib(last):
    """Return whether Mathlib declares a name ending in `last`."""
    pat = re.compile(r"(?:theorem|lemma|def|abbrev)\s+(?:\S+\.)?" + re.escape(last) + r"\b")
    for f in MATHLIB.rglob("*.lean"):
        if last in f.read_text(encoding="utf8", errors="ignore") and \
                pat.search(f.read_text(encoding="utf8", errors="ignore")):
            return True
    return False


def declared_names():
    """Return the set of declaration names, with and without their namespace prefixes."""
    names = set()
    for f in SRC.glob("*.lean"):
        text = f.read_text(encoding="utf8")
        for m in DECL.finditer(text):
            full = m.group(1)
            names.add(full)
            names.add(full.split(".")[-1])
        # structure fields
        for m in re.finditer(r"^structure\s+(\S+)[^\n]*where\n((?:\s+.*\n)+?)\n", text, re.M):
            for fm in re.finditer(r"^\s{2}(\w+)\s*:", m.group(2), re.M):
                names.add(fm.group(1))
    return names


def main():
    errors = []
    modules = sorted(f.stem for f in SRC.glob("*.lean"))
    root_imports = (ROOT / "HolographicUniverse.lean").read_text(encoding="utf8")
    audit = (SRC / "Audit.lean").read_text(encoding="utf8")
    readme = (ROOT / "README.md").read_text(encoding="utf8")
    for mod in modules:
        if mod == "Audit":
            continue
        imp = f"import HolographicUniverse.{mod}\n"
        if imp not in root_imports:
            errors.append(f"{mod}: not imported by HolographicUniverse.lean")
        if imp not in audit:
            errors.append(f"{mod}: not imported by Audit.lean")
        if f"| `{mod}.lean` |" not in readme:
            errors.append(f"{mod}: no row in the README layout table")

    names = declared_names()
    for f in SRC.glob("*.lean"):
        names.update(re.findall(r'^elab\s+"(\w+)"', f.read_text(encoding="utf8"), re.M))
    cited = re.compile(r"`((?:[A-Z]\w*\.)?[a-z]\w*(?:_\w+)+[₀-₉']*|(?:[A-Z]\w*\.)[a-z]\w+[₀-₉']*)`")
    missing = {}
    for doc in DOCS:
        for m in cited.finditer(doc.read_text(encoding="utf8")):
            name = m.group(1)
            last = name.split(".")[-1]
            if name.endswith((".lean", ".md")) or name in EXTERNAL:
                continue
            # Physics symbols such as `r_c`, `n_s`, `f_NL`: every part has at most two letters.
            if "." not in name and all(len(part) <= 2 for part in name.split("_")):
                continue
            if name not in names and last not in names:
                missing.setdefault(last, []).append(f"{doc.relative_to(ROOT)}: `{name}`")
    for last, where in missing.items():
        if not in_mathlib(last):
            errors.extend(f"{w} is not declared" for w in where)

    model = (SRC / "Model.lean").read_text(encoding="utf8")
    block = re.search(r"structure BraneCosmology where\n(.*?)\n\nnamespace", model, re.S).group(1)
    for fm in re.finditer(r"^  (\w+)\s*:", block, re.M):
        field = fm.group(1)
        if field not in {"c", "K", "H0", "rh", "ε", "a", "ρ", "P", "ρt", "Pt"} and \
                f"`BraneCosmology.{field}`" not in readme:
            errors.append(f"README.md: field `BraneCosmology.{field}` is not cited")

    for e in sorted(set(errors)):
        print(e)
    print(f"{len(modules)} modules, {len(set(errors))} problems")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
