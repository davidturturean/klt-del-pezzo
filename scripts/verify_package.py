#!/usr/bin/env python3
"""Verify the package records without running Lean or Lake.

This checks the internal consistency of the packaged complete formalization:
file hashes, the copy manifest, the Lean import closure, the toolchain pins,
the admitted literature axioms, the committed axiom report, the claim registry
and the retained candidate1559 records. It does not establish fresh kernel
verification or manuscript correctness; `lake build KltDP` and
`scripts/print_axioms.sh` on the pinned toolchain remain the kernel checks.
"""

from __future__ import annotations

import collections
import gzip
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
TRUST = "KltDP/Audit/Trust.lean"
MAIN = "KltDP.Manuscript.uniformSevenPointBound"
IGNORED_DIRS = {".git", ".lake", "build", "__pycache__"}
DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(private|protected)\s+)?(?:noncomputable\s+)?(?:nonrec\s+)?"
                     r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|alias)\s+([A-Za-z_][\w.'!?]*)")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def package_files() -> list[Path]:
    return sorted(p for p in ROOT.rglob("*") if p.is_file()
                  and not (set(p.relative_to(ROOT).parts) & IGNORED_DIRS))


def declaration_index(strip) -> dict[str, tuple[str, str]]:
    """Public declarations with namespace tracking; a source heuristic, not Lean name resolution."""
    index: dict[str, tuple[str, str]] = {}
    for file in sorted((ROOT / "KltDP").rglob("*.lean")):
        rel = file.relative_to(ROOT).as_posix()
        if rel == TRUST:
            continue
        stack: list[tuple[str, str]] = []
        for line in strip(file.read_text(encoding="utf-8")).split("\n"):
            m = re.match(r"\s*namespace\s+([\w.]+)", line)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            m = re.match(r"\s*(?:noncomputable\s+)?section\b\s*([\w.]*)", line)
            if m:
                stack.append(("sec", m.group(1)))
                continue
            m = re.match(r"\s*end\b\s*([\w.]*)\s*$", line)
            if m and stack:
                stack.pop()
                continue
            m = DECL_RE.match(line)
            if m:
                vis, kind, name = m.groups()
                if vis == "private":
                    continue
                ns = ".".join(x[1] for x in stack if x[0] == "ns")
                fq = name[len("_root_."):] if name.startswith("_root_.") else (f"{ns}.{name}" if ns else name)
                index.setdefault(fq, (kind, rel))
    return index


def main() -> int:
    failures: list[str] = []

    def check(condition: bool, description: str) -> None:
        if not condition:
            failures.append(description)

    provenance = json.loads((ROOT / "PROVENANCE.json").read_text())
    claims = json.loads((ROOT / "audit/claim-status.json").read_text())
    literature = json.loads((ROOT / "audit/literature-assumptions.json").read_text())
    source_audit = json.loads((ROOT / "audit/source-audit.json").read_text())
    history_dir = ROOT / "audit/checkpoints/candidate1559"
    snapshot = json.loads((history_dir / "snapshot.json").read_text())
    checkpoint = json.loads((history_dir / "production-v4-candidate1559-20260913.json").read_text())
    check(provenance["schema"] == "klt-package-provenance-v2", "PROVENANCE schema is not v2")
    check(claims["schema"] == "klt-public-claim-status-v2", "claim-status schema is not v2")
    check(literature["schema"] == "klt-literature-assumptions-v2", "literature-assumptions schema is not v2")

    # 1. SHA256SUMS and the file set.
    checksum_count = 0
    expected_package_files: set[str] = set()
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        expected, path = line.split("  ", 1)
        target = ROOT / path
        check(target.is_file() and digest(target.read_bytes()) == expected, f"Package checksum mismatch: {path}")
        expected_package_files.add(path)
        checksum_count += 1
    actual_files = {p.relative_to(ROOT).as_posix() for p in package_files() if p.name != "SHA256SUMS"}
    check(actual_files == expected_package_files, "File set differs from SHA256SUMS")

    # 2. Copy manifest.
    copied_paths = set()
    for record in provenance["copied_files"]:
        target = ROOT / record["path"]
        copied_paths.add(record["path"])
        if not target.is_file():
            failures.append(f"Copy manifest names a missing file: {record['path']}")
            continue
        data = target.read_bytes()
        check(digest(data) == record["sha256"], f"Copy manifest mismatch: {record['path']}")
        check(len(data) == record["bytes"], f"Copy manifest byte-count mismatch: {record['path']}")
        if record["transformation"].startswith("gzip"):
            check(digest(gzip.decompress(data)) == record["source_sha256"], "Compressed copy source mismatch")
    generated = set(provenance["generated_files"])
    check(copied_paths.isdisjoint(generated), "A file is both copied and generated")
    check(copied_paths | generated | {"SHA256SUMS"} == actual_files | {"SHA256SUMS"},
          "Copy manifest plus generated files do not cover the package")

    # 3. Lean sources, root coverage and import closure (comment-aware).
    lexer = load_module("klt_source_lexer", ROOT / "scripts/audit_sources.py")
    placeholders = load_module("klt_placeholders", ROOT / "scripts/check_no_placeholders.py")
    lean_paths = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / "KltDP").rglob("*.lean"))
    library = [p for p in lean_paths if p != TRUST]
    snap = provenance["source_snapshot"]
    check(len(library) == snap["modules_total"], "Library module count differs from PROVENANCE")
    check(sum(t["modules"] for t in snap["trees"]) == snap["modules_total"], "Tree module counts do not sum to the total")
    tree_counts = collections.Counter(r["source_tree"] for r in provenance["copied_files"]
                                      if r["path"].startswith("KltDP/") and r["path"] != TRUST)
    check({t["name"]: t["modules"] for t in snap["trees"]} == dict(tree_counts), "Per-tree copy counts differ from PROVENANCE trees")
    check(TRUST in lean_paths and TRUST in copied_paths, "Audit tooling module missing")
    root_text = (ROOT / "KltDP.lean").read_text()
    root_imports = re.findall(r"(?m)^import\s+([\w.]+)\s*$", lexer.mask_noncode(root_text))
    modules = [p[:-5].replace("/", ".") for p in library]
    check(root_imports == sorted(modules), "Root module does not import exactly the sorted library modules")
    check(len(root_text.splitlines()) == len(modules), "Root module has lines other than imports")
    local_imports = 0
    scan_paths = lean_paths + ["KltDP.lean", "audit/CompiledTrust.lean"]
    for path in scan_paths:
        code = lexer.mask_noncode((ROOT / path).read_text())
        for module in re.findall(r"(?m)^\s*import\s+([\w.]+)", code):
            if module == "KltDP" or module.startswith("KltDP."):
                local_imports += 1
                check((ROOT / (module.replace(".", "/") + ".lean")).is_file(), f"Missing local import: {path} -> {module}")

    # 4. Placeholder scan re-run in-process and compared with the committed record.
    scan_findings, allowed_axioms, parse_errors = [], [], []
    allowlist = set(placeholders.LITERATURE_AXIOM_FILES)
    for path in lean_paths + ["KltDP.lean"]:
        src = (ROOT / path).read_text(encoding="utf-8")
        try:
            code = placeholders.strip_noncode(src)
        except ValueError as exc:
            parse_errors.append(f"{path}: {exc}")
            continue
        scan_findings.extend(placeholders.locations(code, placeholders.PLACEHOLDER_RE, "placeholder", path))
        scan_findings.extend(placeholders.locations(code, placeholders.NATIVE_RE, "native_evaluator", path))
        for item in placeholders.locations(code, placeholders.AXIOM_RE, "axiom", path):
            (allowed_axioms if path in allowlist else scan_findings).append(item)
        scan_findings.extend(placeholders.locations(code, placeholders.CONSTANT_RE, "constant", path))
    check(not scan_findings and not parse_errors, "Placeholder scan reports active sorry/admit/native-evaluator/axiom/constant outside the allowlist")
    check(len(allowed_axioms) == 28 and {a["file"] for a in allowed_axioms} == allowlist,
          "Allowlisted literature files do not contain exactly 28 axiom declarations")
    check(collections.Counter(a["file"] for a in allowed_axioms) == {f: 1 for f in allowlist},
          "An allowlisted literature file does not contain exactly one axiom")
    check(source_audit["counts"]["allowed_literature_axioms"] == 28 and source_audit["findings"] == []
          and source_audit["parse_errors"] == [] and source_audit["files_scanned"] == len(lean_paths) + 1
          and sorted((a["file"], a["name"]) for a in source_audit["allowed_literature_axioms"])
          == sorted((a["file"], a["name"]) for a in allowed_axioms),
          "Committed audit/source-audit.json differs from a fresh scan")

    # 5. Literature axioms: names, files, hashes and the trust boundary of check_axioms.py.
    axioms_checker = load_module("klt_check_axioms", ROOT / "scripts/check_axioms.py")
    literature_names = {}
    for file in allowlist:
        stack: list[str] = []
        for line in placeholders.strip_noncode((ROOT / file).read_text(encoding="utf-8")).split("\n"):
            m = re.match(r"\s*namespace\s+([\w.]+)", line)
            if m:
                stack.append(m.group(1))
                continue
            m = re.match(r"\s*end\s+([\w.]+)\s*$", line)
            if m and stack and stack[-1] == m.group(1):
                stack.pop()
                continue
            m = re.match(r"\s*axiom\s+([\w.]+)", line)
            if m:
                literature_names[".".join(stack + [m.group(1)])] = file
    check(set(literature_names) == axioms_checker.LITERATURE, "Literature axiom names differ from check_axioms.py")
    entries = literature["active_literature_axioms"]
    check([e["name"] for e in entries] == sorted(literature_names), "literature-assumptions.json does not list the 28 axioms")
    for entry in entries:
        check(literature_names.get(entry["name"]) == entry["source_path"], f"Literature source path differs: {entry['name']}")
        check(digest((ROOT / entry["source_path"]).read_bytes()) == entry["source_sha256"], f"Literature source hash differs: {entry['name']}")
    check(set(literature["ordinary_axioms"]) == axioms_checker.STANDARD, "Ordinary axiom list differs from check_axioms.py")

    # 6. The committed axiom report.
    report_text = (ROOT / "audit/axiom-report.txt").read_text()
    reports = dict(axioms_checker.REPORT_RE.findall(report_text))
    check("sorryAx" not in report_text, "Axiom report contains sorryAx")
    check(MAIN in reports, "Axiom report lacks the main theorem")
    if MAIN in reports:
        deps = {x.strip() for x in reports[MAIN].replace("\n", " ").split(",") if x.strip()}
        check(deps == axioms_checker.ALLOWED, "Main-theorem dependency set differs from the allowed trust boundary")
    for record in provenance["copied_files"]:
        if record["path"] == "audit/axiom-report.txt":
            check(record["sha256"] == digest(report_text.encode()), "Axiom report hash differs from PROVENANCE")

    # 7. Claim registry.
    index = declaration_index(placeholders.strip_noncode)
    rows = claims["results"]
    check(len(rows) == 119, "Expected 119 claim rows")
    counts = collections.Counter((x["kind"], x["status"]) for x in rows)
    named_total = sum(v for (k, _), v in counts.items() if k == "named_result")
    check(named_total == 47 and counts[("named_result", "complete")] + counts[("named_result", "complete_with_isolated_clauses")] == 47,
          "Named results are not all complete or complete_with_isolated_clauses")
    check(counts[("unnumbered_supporting_obligation", "complete")] == 32
          and counts[("unnumbered_supporting_obligation", "superseded_by_named_results")] == 40,
          "Support obligation counts differ from 32 accepted + 40 superseded")
    check(claims["manuscript_complete"] is True and claims["main_theorem"]["declaration"] == MAIN, "Registry main-theorem record differs")
    main_row = next(x for x in rows if x["id"] == "thm:main")
    check(main_row["status"] == "complete" and MAIN in main_row["compiled_declarations"], "thm:main is not complete with the main theorem")
    main_record = next((r for r in main_row["declaration_records"] if r["name"] == MAIN), None)
    check(main_record is not None and set(main_record["axioms"]) == axioms_checker.ALLOWED, "thm:main declaration record axioms differ from the report")
    tex_sha = digest((ROOT / "source/manuscript.tex").read_bytes())
    declaration_links = 0
    unresolved = []
    for row in rows:
        check(row["source"]["sha256"] == tex_sha, f"Row source hash differs: {row['id']}")
        check(len(row["compiled_declarations"]) == len(row["declaration_records"]), f"Declaration record count differs: {row['id']}")
        if row["status"] == "superseded_by_named_results":
            check(not row["compiled_declarations"], f"Superseded row lists declarations: {row['id']}")
        if row["status"] == "complete_with_isolated_clauses":
            check(bool(row.get("isolated_clauses")), f"No isolated clauses recorded: {row['id']}")
        for record in row["declaration_records"]:
            declaration_links += 1
            path = record["source_path"]
            check((ROOT / path).is_file(), f"Declaration source missing: {row['id']} -> {path}")
            check(record["module"] == path[:-5].replace("/", "."), f"Module/path mismatch: {record['name']}")
            name = record["name"]
            if name in index:
                check(index[name][1] == path, f"Declaration found in another file: {name} ({index[name][1]} vs {path})")
                continue
            leaf = name.rsplit(".", 1)[-1]
            text = (ROOT / path).read_text(encoding="utf-8") if (ROOT / path).is_file() else ""
            if not re.search(r"(?m)^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                             r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|alias)\s+(?:[\w.]+\.)?"
                             + re.escape(leaf) + r"(?=[\s(\[{:])", text):
                unresolved.append(f"{row['id']} -> {name}")
    check(not unresolved, "Claim declarations not found in their recorded source files")

    # 8. Toolchain pins.
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")["rev"]
    lakefile = (ROOT / "lakefile.toml").read_text()
    check(toolchain == snap["lean_toolchain"] == snapshot["lean_toolchain"], "Lean toolchain pin differs")
    check(mathlib == snap["mathlib_commit"] == snapshot["mathlib_commit"] and f'rev = "{mathlib}"' in lakefile, "Mathlib pin differs")

    # 9. Retained candidate1559 records (historical; the tree is no longer bound to them).
    # The retained records name their original paths; they now live under audit/checkpoints/candidate1559/.
    archive = gzip.decompress((history_dir / Path(snapshot["certificate"]["path"]).name).read_bytes())
    check((history_dir / "candidate1559_root_acceptance.json").is_file(), "Retained acceptance record missing")
    check(digest(archive) == checkpoint["validation_sha256"] == snapshot["certificate"]["uncompressed_sha256"],
          "Retained certificate differs from the checkpoint hash")
    certificate = json.loads(archive)
    for package in manifest["packages"]:
        check(certificate["dependencies"][package["name"]] == package["rev"], f"Dependency pin differs from the retained certificate: {package['name']}")
    changed = {c["path"]: c for c in snap["modules_changed_since_candidate1559"]}
    history = provenance["history"]["candidate1559"]
    check(len(checkpoint["sources"]) == 1561 and len(history["copied_files"]) == 1584, "Historical record sizes differ")
    historical_changes = 0
    for path, expected in checkpoint["sources"].items():
        file = ROOT / path
        if path == "KltDP.lean":
            continue
        if file.is_file() and digest(file.read_bytes()) != expected:
            historical_changes += 1
            check(path in changed and changed[path]["candidate1559_sha256"] == expected,
                  f"Module changed since candidate1559 without a PROVENANCE record: {path}")
    check(historical_changes == len(changed), "PROVENANCE changed-module list differs from the checkpoint comparison")
    for row in rows:
        if row["kind"] == "named_result" and not row.get("formalization_record") or row["status"] == "complete" and row["kind"] != "named_result":
            for record in row["declaration_records"]:
                check(record.get("present_in_current_certificate") is True, f"Retained record lost its certificate flag: {row['id']}")

    # 10. Markdown links.
    broken_links = []
    for path in ROOT.rglob("*.md"):
        if set(path.relative_to(ROOT).parts) & IGNORED_DIRS:
            continue
        for href in re.findall(r"\[[^\]]*\]\(([^)]+)\)", path.read_text()):
            if re.match(r"(?:https?:|mailto:|#)", href):
                continue
            filename = href.split("#", 1)[0]
            if filename and not (path.parent / filename).exists():
                broken_links.append(f"{path.relative_to(ROOT)} -> {href}")
    check(not broken_links, "Broken local Markdown links")

    report = {"status": "passed" if not failures else "failed",
              "scope": "Package integrity and record correspondence; no Lean/Lake execution",
              "snapshot_date": provenance["snapshot_date"], "package_files_hashed": checksum_count,
              "library_modules": len(library), "root_imports": len(root_imports), "local_imports_resolved": local_imports,
              "literature_axioms": len(allowed_axioms), "claim_rows": len(rows), "declaration_links": declaration_links,
              "modules_changed_since_candidate1559": sorted(changed), "placeholder_findings": scan_findings,
              "unresolved_declarations": unresolved, "broken_links": broken_links, "failures": failures}
    print(json.dumps(report, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
