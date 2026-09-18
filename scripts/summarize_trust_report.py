#!/usr/bin/env python3
"""Stream a #klt_trust_report log once and summarize it; diagnostic only, not a certificate.

usage: summarize_trust_report.py BUILD_LOG OUT_JSON [ALLOWLIST_JSON]
Extracts the BEGIN/AUDIT records, every KLT_TRUST_FAILURE record, per-scope counts, the set of
transitive axioms over logical roots, the modules of failing roots, and the axiom sets of a
few named roots. It does not validate record shapes; that is the parser's job.
"""
import collections
import json
import sys
from pathlib import Path

log, out = Path(sys.argv[1]), Path(sys.argv[2])
allow = set(json.loads(Path(sys.argv[3]).read_text())) if len(sys.argv) > 3 else None
NAMED = {"KltDP.Manuscript.uniformSevenPointBound", "KltDP.Manuscript.S01.sharpnessExampleCharThree",
         "KltDP.Manuscript.S01.characteristicTwoFamily"}
begin = summary = None
by_name_failed = {}
end = None
failures, named = [], {}
error_lines, other_lines = [], []
scopes = collections.Counter()
kinds = collections.Counter()
axioms_over_logical = set()
non_allowlisted_roots = []
decl_count = 0
modules = set()
lines = 0
with log.open("rb") as stream:
    for raw in stream:
        lines += 1
        line = raw.decode("utf-8", "replace")
        if not line.startswith("KLT_TRUST_"):
            stripped = line.strip()
            if stripped and "error" in stripped:
                error_lines.append({"line": lines, "text": stripped[:400]})
            elif stripped and not stripped.startswith("Running as unit:"):
                other_lines.append({"line": lines, "text": stripped[:200]})
            continue
        tag, _, payload = line.partition(" ")
        payload = payload.strip()
        if tag == "KLT_TRUST_INVENTORY_BEGIN":
            begin = json.loads(payload)
        elif tag == "KLT_TRUST_INVENTORY_END":
            end = json.loads(payload)
        elif tag == "KLT_TRUST_AUDIT":
            summary = json.loads(payload)
        elif tag == "KLT_TRUST_FAILURE":
            row = json.loads(payload)
            failures.append(row)
        elif tag == "KLT_TRUST_DECL":
            row = json.loads(payload)
            decl_count += 1
            scopes[row.get("scope")] += 1
            kinds[row.get("kind")] += 1
            modules.add(row.get("module"))
            if row.get("root_policy_passes") is False:
                by_name_failed[row["name"]] = {k: row.get(k) for k in ("module", "kind", "partial", "unsafe", "root_policy_passes")}
            if row.get("scope") in {"mathematical_declaration", "safe_definition_runtime_companion"}:
                closure = row.get("closure") or {}
                ax = set(closure.get("transitive_axioms", []))
                axioms_over_logical |= ax
                if allow is not None and not ax <= allow:
                    non_allowlisted_roots.append({"name": row["name"], "module": row["module"],
                                                  "axioms": sorted(ax - allow)})
            if row.get("name") in NAMED:
                closure = row.get("closure") or {}
                named[row["name"]] = {"module": row.get("module"), "kind": row.get("kind"),
                                      "root_policy_passes": row.get("root_policy_passes"),
                                      "transitive_axioms": closure.get("transitive_axioms"),
                                      "closure_passes": closure.get("passes"),
                                      "dependency_count": closure.get("transitive_dependency_count_including_root")}
failure_modules = collections.Counter()
failure_rows = []
for row in failures:
    name = row.get("name")
    closure = row.get("closure") or {}
    row = by_name_failed.get(name, {})
    failure_rows.append({"name": name, "module": row.get("module"), "kind": row.get("kind"),
                         "partial": row.get("partial"), "unsafe": row.get("unsafe"),
                         "root_policy_passes": row.get("root_policy_passes"),
                         "partial_dependencies": closure.get("partial_dependencies"),
                         "unsafe_dependencies": closure.get("unsafe_dependencies"),
                         "forbidden_axioms": closure.get("forbidden_axioms"),
                         "missing_checked_declarations": closure.get("missing_checked_declarations"),
                         "audit_tooling_dependencies": closure.get("audit_tooling_dependencies")})
result = {"schema": "klt-trust-report-summary-v1",
          "status": "raw_trust_report_summary_not_a_certificate",
          "log": str(log), "physical_lines": lines, "begin": begin, "end": end, "summary": summary,
          "lean_error_lines": error_lines, "other_untagged_lines": other_lines[:50],
          "declaration_rows": decl_count, "scope_counts": dict(scopes), "kind_counts": dict(kinds),
          "module_count": len(modules), "transitive_axioms_over_logical_roots": sorted(axioms_over_logical),
          "logical_roots_with_non_allowlisted_axioms": non_allowlisted_roots,
          "failure_count": len(failures), "failures": failure_rows, "named_roots": named}
out.write_text(json.dumps(result, indent=1) + "\n")
result["rejected_root_rows"] = len(by_name_failed)
result["rejected_root_rows_not_in_failure_records"] = sorted(set(by_name_failed) - {f.get("name") for f in failures})
print(json.dumps({k: result[k] for k in ("physical_lines", "declaration_rows", "scope_counts", "failure_count", "module_count", "rejected_root_rows")}))
print("summary:", json.dumps(summary)[:1500] if summary else None)
print("named:", json.dumps(named)[:2000])
