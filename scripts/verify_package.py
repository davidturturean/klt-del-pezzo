#!/usr/bin/env python3
"""Verify source/archive correspondence without running Lean or Lake.

This checks the consistency of a packaged checkpoint and its retained evidence.
It does not establish fresh kernel verification or manuscript correctness.
"""

from __future__ import annotations

import collections
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    failures: list[str] = []

    def check(condition: bool, description: str) -> None:
        if not condition:
            failures.append(description)

    snapshot = json.loads((ROOT / "audit/snapshot.json").read_text())
    checkpoint = json.loads((ROOT / "audit/checkpoints/production-v4-candidate1559-20260913.json").read_text())
    provenance = json.loads((ROOT / "PROVENANCE.json").read_text())
    claims = json.loads((ROOT / "audit/claim-status.json").read_text())
    literature = json.loads((ROOT / "audit/literature-assumptions.json").read_text())
    archive = gzip.decompress((ROOT / snapshot["certificate"]["path"]).read_bytes())
    check(digest(archive) == checkpoint["validation_sha256"], "Certificate differs from checkpoint hash")
    certificate = json.loads(archive)

    checksum_count = 0
    expected_package_files: set[str] = set()
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        expected, path = line.split("  ", 1)
        target = ROOT / path
        check(target.is_file() and digest(target.read_bytes()) == expected, f"Package checksum mismatch: {path}")
        expected_package_files.add(path)
        checksum_count += 1
    ignored_dirs = {".git", ".lake", "build", "__pycache__"}
    actual_files = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*")
                    if p.is_file() and not any(x in ignored_dirs for x in p.relative_to(ROOT).parts)
                    and p.name != "SHA256SUMS"}
    check(actual_files == expected_package_files, "File set differs from SHA256SUMS")

    for record in provenance["copied_files"]:
        target = ROOT / record["path"]
        data = target.read_bytes()
        check(digest(data) == record["sha256"], f"Copy manifest mismatch: {record['path']}")
        check(len(data) == record["bytes"], f"Copy manifest byte-count mismatch: {record['path']}")
        if record["transformation"].startswith("gzip"):
            check(digest(gzip.decompress(data)) == record["source_sha256"], "Compressed copy source mismatch")

    source_bindings = checkpoint["sources"]
    for path, expected in source_bindings.items():
        file = ROOT / path
        check(file.is_file() and digest(file.read_bytes()) == expected, f"Checkpoint source mismatch: {path}")
    check(source_bindings == certificate["sources"]["audited_sources"], "Certificate/checkpoint source sets differ")
    lean_paths = {p.relative_to(ROOT).as_posix() for p in (ROOT / "KltDP").rglob("*.lean")}
    lean_paths.add("KltDP.lean")
    check(lean_paths == set(source_bindings), "Packaged production Lean source set differs from checkpoint")
    check(len(source_bindings) == 1561, "Expected 1,561 audited source files")

    spec = importlib.util.spec_from_file_location("klt_source_lexer", ROOT / "scripts/audit_sources.py")
    assert spec is not None and spec.loader is not None
    lexer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(lexer)
    check(digest((ROOT / "scripts/audit_sources.py").read_bytes()) == checkpoint["source_gate_sha256"],
          "Source lexer differs from accepted version")
    local_imports = 0
    placeholder_hits = []
    axiom_sources = []
    forbidden = {"sorry", "admit", "sorryAx", "native_decide", "native_eval", "skipKernelTC", "addDeclWithoutChecking"}
    for path in sorted(lean_paths):
        text = (ROOT / path).read_text()
        code = lexer.mask_noncode(text)
        for module in re.findall(r"(?m)^\s*import\s+([\w.]+)", code):
            if module == "KltDP" or module.startswith("KltDP."):
                local_imports += 1
                check((ROOT / (module.replace(".", "/") + ".lean")).is_file(), f"Missing local import: {path} -> {module}")
        if path == "KltDP/Audit/Trust.lean":
            continue
        for finding in lexer.findings(text):
            if finding["token"] in forbidden:
                placeholder_hits.append({"path": path, **finding})
        for name in re.findall(r"(?m)^\s*axiom\s+([\w.]+)", code):
            axiom_sources.append((path, name))
    check(not placeholder_hits, "Forbidden postponed/native proof tokens in mathematical sources")
    expected_axioms = {(x["source_path"], x["name"].split(".")[-1]) for x in literature["active_literature_axioms"]}
    check(set(axiom_sources) == expected_axioms and len(axiom_sources) == 4, "Source axiom declarations differ from four-entry inventory")
    for entry in literature["active_literature_axioms"]:
        check(digest((ROOT / entry["source_path"]).read_bytes()) == entry["source_sha256"], f"Literature source mismatch: {entry['name']}")

    allowed = set(literature["ordinary_axioms"]) | {x["name"] for x in literature["active_literature_axioms"]}
    check(set(certificate["inventory_summary"]["transitive_axioms"]) == allowed, "Certificate trust boundary differs from assumptions inventory")
    check(certificate["inventory_summary"]["failed_declaration_count"] == 0, "Certificate records failed declarations")
    check(certificate["inventory_summary"]["mathematical_declaration_count"] == 28595, "Mathematical declaration count differs")

    declared = {x["name"] for x in certificate["public_declaration_index"]}
    declared.update(x["user_name"] for x in certificate["public_declaration_index"])
    declaration_links = 0
    for row in claims["results"]:
        for name in row["compiled_declarations"]:
            check(name in declared, f"Accepted declaration absent from certificate: {row['id']} -> {name}")
            declaration_links += 1
        if row["status"] == "specified":
            check(not row["compiled_declarations"], f"Specified row has accepted declarations: {row['id']}")
    counts = collections.Counter((x["kind"], x["status"]) for x in claims["results"])
    check(len(claims["results"]) == 119, "Expected 119 claim rows")
    check(counts == {("named_result", "complete"): 4, ("named_result", "specified"): 43,
                     ("unnumbered_supporting_obligation", "complete"): 32,
                     ("unnumbered_supporting_obligation", "specified"): 40}, "Claim-status counts differ")
    check(claims["manuscript_complete"] is False, "Claim registry incorrectly marks manuscript complete")
    for key in ["thm:main", "thm:examples"]:
        check(next(x for x in claims["results"] if x["id"] == key)["status"] == "specified", f"Endpoint status changed: {key}")

    check((ROOT / "lean-toolchain").read_text().strip() == snapshot["lean_toolchain"], "Lean toolchain pin differs")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    check(next(p for p in manifest["packages"] if p["name"] == "mathlib")["rev"] == snapshot["mathlib_commit"], "Mathlib pin differs")
    for package in manifest["packages"]:
        check(certificate["dependencies"][package["name"]] == package["rev"], f"Dependency pin differs: {package['name']}")

    broken_links = []
    for path in ROOT.rglob("*.md"):
        for href in re.findall(r"\[[^\]]*\]\(([^)]+)\)", path.read_text()):
            if re.match(r"(?:https?:|mailto:|#)", href):
                continue
            filename = href.split("#", 1)[0]
            if filename and not (path.parent / filename).exists():
                broken_links.append(f"{path.relative_to(ROOT)} -> {href}")
    check(not broken_links, "Broken local Markdown links")

    report = {"status": "passed" if not failures else "failed",
              "scope": "Package integrity and archived-record correspondence; no Lean/Lake execution",
              "source_commit": snapshot["source_commit"], "checkpoint": snapshot["checkpoint"],
              "package_files_hashed": checksum_count, "audited_sources_matched": len(source_bindings),
              "mathematical_modules": len(source_bindings)-2, "local_imports_resolved": local_imports,
              "claim_rows": len(claims["results"]), "accepted_declaration_links": declaration_links,
              "literature_axioms": len(axiom_sources), "placeholder_hits": placeholder_hits,
              "broken_links": broken_links, "failures": failures}
    print(json.dumps(report, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
