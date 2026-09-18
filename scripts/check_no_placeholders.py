#!/usr/bin/env python3
"""Comment-aware static audit of Lean source.

The scanner removes nested block comments, line comments, strings, and
character literals before reporting active `sorry`, `admit`, native
evaluator proof paths (`native_decide`, `native_eval`, `ofReduce*`),
top-level `axiom`, or top-level `constant` declarations. Top-level `axiom` declarations
are permitted only in the literature modules listed in
`LITERATURE_AXIOM_FILES`, each of which must contain exactly one. It is a
source audit; `lake build` and `#print axioms` remain the kernel-level checks.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# The admitted literature statements. Every other file must be axiom-free.
LITERATURE_AXIOM_FILES = (
    "KltDP/Literature/Hartshorne/HurwitzDegreeTwoInstance.lean",
    "KltDP/Literature/Hartshorne/IntegralNumericalGroup.lean",
    "KltDP/Literature/Hartshorne/MinimalSurfaceClassification.lean",
    "KltDP/Literature/Hartshorne/PointBlowupCohomology.lean",
    "KltDP/Literature/Hartshorne/RuledSurfaceGenus.lean",
    "KltDP/Literature/Hartshorne/RuledSurfacePicard.lean",
    "KltDP/Literature/Hartshorne/StrictTransformInstance.lean",
    "KltDP/Literature/Hartshorne/SurfaceHodgeIndex.lean",
    "KltDP/Literature/Hartshorne/SurfaceNakaiMoishezon.lean",
    "KltDP/Literature/Hartshorne/SurfaceProjectivity.lean",
    "KltDP/Literature/Hartshorne/SurfaceRiemannRoch.lean",
    "KltDP/Literature/HartshorneCastelnuovoLiteral.lean",
    "KltDP/Literature/KeelCompleteSystem.lean",
    "KltDP/Literature/LipmanResolutionLiteral.lean",
    "KltDP/Literature/ProperCurvePullbackDegreeLiteral.lean",
    "KltDP/Literature/RegularSmoothLociLiteral.lean",
    "KltDP/Literature/SmoothStandardCoverLiteral.lean",
    "KltDP/Literature/Stacks/AffineMorphismCohomology.lean",
    "KltDP/Literature/Stacks/BlowupRegularPointAdmitted.lean",
    "KltDP/Literature/Stacks/CurveTensorDegreeLiteral.lean",
    "KltDP/Literature/Stacks/FieldJ2.lean",
    "KltDP/Literature/Stacks/ProperCohomologyFinite.lean",
    "KltDP/Literature/Stacks/ProperFlatFiberEuler.lean",
    "KltDP/Literature/Stacks/RegularLocalUFD.lean",
    "KltDP/Literature/StacksPointBlowupDomination.lean",
    "KltDP/Literature/SteinFactorizationNoetherian.lean",
    "KltDP/Literature/Tanaka/ContractionTheorem.lean",
    "KltDP/Literature/ZariskiNormalCompletion.lean",
)


def strip_noncode(src: str) -> str:
    out: list[str] = []
    i = 0
    n = len(src)
    block_depth = 0
    state = "code"
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if block_depth:
            if c == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif c == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if state == "string":
            if c == "\\":
                out.append(" ")
                if i + 1 < n:
                    out.append("\n" if src[i + 1] == "\n" else " ")
                i += 2
            elif c == '"':
                out.append(" ")
                state = "code"
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if state == "char":
            if c == "\\":
                out.append(" ")
                if i + 1 < n:
                    out.append(" ")
                i += 2
            elif c == "'":
                out.append(" ")
                state = "code"
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if c == "-" and nxt == "-":
            out.extend("  ")
            i += 2
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if c == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        if c == '"':
            state = "string"
            out.append(" ")
            i += 1
            continue
        # A conservative character-literal test. Apostrophes inside Lean
        # identifiers are left alone.
        prev = src[i - 1] if i else " "
        if c == "'" and (prev.isspace() or prev in "([{,:="):
            state = "char"
            out.append(" ")
            i += 1
            continue
        out.append(c)
        i += 1
    if block_depth:
        raise ValueError("unterminated block comment")
    if state != "code":
        raise ValueError(f"unterminated {state} literal")
    return "".join(out)


PLACEHOLDER_RE = re.compile(r"\b(?:sorry|admit)\b")
NATIVE_RE = re.compile(r"(?<![\w.'])(?:native_decide|native_eval|ofReduce\w*)\b")
AXIOM_RE = re.compile(r"(?m)^(?:(?:private|protected)\s+)?axioms?\s+([^\s(\[{:]+)")
# `constant` can also introduce an assumption. Restrict to column zero so a
# structure field named `constant` is not misclassified.
CONSTANT_RE = re.compile(r"(?m)^(?:(?:private|protected)\s+)?constants?\s+[A-Za-z_«]")


def locations(text: str, regex: re.Pattern[str], kind: str, path: str) -> list[dict]:
    found = []
    for match in regex.finditer(text):
        line = text.count("\n", 0, match.start()) + 1
        last_nl = text.rfind("\n", 0, match.start())
        column = match.start() - last_nl
        item = {"kind": kind, "file": path, "line": line, "column": column}
        if kind == "axiom":
            item["name"] = match.group(1)
        found.append(item)
    return found


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--json", dest="json_path", type=Path)
    args = parser.parse_args()

    files: list[Path] = []
    for path in args.paths:
        if path.is_file() and path.suffix == ".lean":
            files.append(path)
        elif path.is_dir():
            files.extend(path.rglob("*.lean"))
    files = sorted(set(files))

    findings: list[dict] = []
    allowed_axioms: list[dict] = []
    parse_errors: list[dict] = []
    allowlist = set(LITERATURE_AXIOM_FILES)
    axioms_per_allowed_file = {path: 0 for path in LITERATURE_AXIOM_FILES}
    for path in files:
        rel = path.as_posix()
        src = path.read_text(encoding="utf-8")
        try:
            code = strip_noncode(src)
        except ValueError as exc:
            parse_errors.append({"file": rel, "error": str(exc)})
            continue
        findings.extend(locations(code, PLACEHOLDER_RE, "placeholder", rel))
        findings.extend(locations(code, NATIVE_RE, "native_evaluator", rel))
        for item in locations(code, AXIOM_RE, "axiom", rel):
            if rel in allowlist:
                axioms_per_allowed_file[rel] += 1
                allowed_axioms.append(item)
            else:
                findings.append(item)
        findings.extend(locations(code, CONSTANT_RE, "constant", rel))
    for rel, count in axioms_per_allowed_file.items():
        if count != 1:
            findings.append({"kind": "allowlist", "file": rel, "line": 0, "column": 0,
                             "detail": f"expected exactly one axiom declaration, found {count}"})

    counts = {
        "sorry_or_admit": sum(item["kind"] == "placeholder" for item in findings),
        "native_evaluator": sum(item["kind"] == "native_evaluator" for item in findings),
        "axiom_declarations_outside_allowlist": sum(item["kind"] == "axiom" for item in findings),
        "allowlist_violations": sum(item["kind"] == "allowlist" for item in findings),
        "constant_declarations": sum(item["kind"] == "constant" for item in findings),
        "allowed_literature_axioms": len(allowed_axioms),
        "parse_errors": len(parse_errors),
    }
    report = {
        "files_scanned": len(files),
        "counts": counts,
        "literature_axiom_files": list(LITERATURE_AXIOM_FILES),
        "allowed_literature_axioms": allowed_axioms,
        "findings": findings,
        "parse_errors": parse_errors,
    }
    if args.json_path:
        args.json_path.parent.mkdir(parents=True, exist_ok=True)
        args.json_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(f"Scanned {len(files)} Lean files.")
    print("Counts: " + ", ".join(f"{key}={value}" for key, value in counts.items()))
    for item in allowed_axioms:
        print(f"{item['file']}:{item['line']}: allowed literature axiom {item['name']}")
    for item in findings:
        detail = item.get("detail") or f"active {item['kind']}" + (f" {item['name']}" if "name" in item else "")
        print(f"{item['file']}:{item['line']}:{item['column']}: {detail}")
    for item in parse_errors:
        print(f"{item['file']}: {item['error']}")
    return 1 if findings or parse_errors else 0


if __name__ == "__main__":
    sys.exit(main())
