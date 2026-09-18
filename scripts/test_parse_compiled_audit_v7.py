#!/usr/bin/env python3
"""Synthetic regression tests for the policy-v7 parser; never Lean proof evidence.

All fixtures are in-memory or temporary-directory data: a synthetic inventory
with the twenty-eight registered axiom rows and a synthetic registry. No Lean
process, VM record or production report is used or produced.
"""

import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parent


def module(name, path):
    from types import ModuleType
    result = ModuleType(name)
    result.__file__ = str(path)
    exec(compile(Path(path).read_bytes(), str(path), "exec"), result.__dict__)
    return result


P = module("compiled_audit_parser_v7", ROOT / "parse_compiled_audit256cpu4.py")
HISTORICAL_ROOT = Path("/Users/davidturturean/Documents/Codingprojects/KltDelPezzoLean")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def closure():
    return {"passes": True, "transitive_dependency_count_including_root": 1,
            "transitive_axioms": [], "forbidden_axioms": [], "missing_checked_declarations": [],
            "unsafe_dependencies": [], "partial_dependencies": [], "audit_tooling_dependencies": [],
            "opaque_dependencies": [], "runtime_override_dependencies": []}


def declaration(name="KltDP.Synthetic.owner"):
    return {"name": name, "user_name": name, "module": "KltDP.Synthetic",
            "scope": "mathematical_declaration", "checked": True, "kind": "definition",
            "universe_parameters": [], "type": "Nat → Nat", "type_expression": "synthetic_type_only",
            "direct_dependencies": [], "unsafe": False, "partial": False, "extern": False,
            "implemented_by": None, "source_range_present": True, "noncomputable": False,
            "reducibility_hints": "regular", "compiler_cache_owner": None, "compiler_cache_stage": None,
            "root_policy_passes": True, "closure": closure()}


def literal_type(name):
    return f"SYNTHETIC printed type of {name}", f"SYNTHETIC raw expression of {name}"


def axiom_row(name):
    row = declaration(name)
    printed, raw = literal_type(name)
    row.update(module=P.LITERATURE_MODULES[name], kind="axiom", reducibility_hints=None,
               universe_parameters=["u"], type=printed, type_expression=raw)
    row["closure"]["transitive_axioms"] = [name]
    return row


def source_bytes(name):
    return f"axiom {name} : True\n".encode()


def registry_entries():
    entries = []
    for name in P.LITERATURE_NAMES:
        printed, raw = literal_type(name)
        entry = {"name": name, "module": P.LITERATURE_MODULES[name], "source_path": P.source_path(name),
                 "source_sha256": sha(source_bytes(name)), "universe_parameters": ["u"],
                 "type_expression_sha256": sha(raw.encode()), "printed_type_sha256": sha(printed.encode()),
                 "published_source": {"reference": "SYNTHETIC", "theorem": "none"}}
        if name in P.HISTORICAL_REGISTRIES:
            path, digest = P.HISTORICAL_REGISTRIES[name]
            entry["original_registry"] = {"path": path, "sha256": digest}
        entries.append(entry)
    return entries


def registry(entries=None):
    return {"schema": P.LITERATURE_REGISTRY_SCHEMA, "policy": P.CACHE_POLICY,
            "ordinary_axioms": sorted(P.FOUNDATIONS),
            "active_literature_axioms": entries if entries is not None else registry_entries(),
            "authority": "SYNTHETIC test registry", "proof_status": "synthetic"}


def fixture(extra=None):
    decls = [declaration()] + (extra or []) + [axiom_row(name) for name in P.LITERATURE_NAMES]
    mathematical = [d for d in decls if d["scope"] == "mathematical_declaration"]
    begin = {"schema": P.SCHEMA, "compiler_cache_policy": P.CACHE_POLICY,
             "foundational_axioms": sorted(P.FOUNDATIONS), "literature_axioms": list(P.LITERATURE_NAMES),
             "declaration_count": len(decls), "scope": "SYNTHETIC parser regression only"}
    axioms = sorted({a for d in mathematical for a in d["closure"]["transitive_axioms"]})
    summary = {"schema": P.SCHEMA, "compiler_cache_policy": P.CACHE_POLICY,
               "mathematical_declaration_count": len(mathematical), "runtime_companion_count": 0,
               "compiler_stage_cache_count": 0, "unsafe_implementation_count": 0,
               "failed_declaration_count": 0, "transitive_axioms": axioms,
               "literature_axioms": list(P.LITERATURE_NAMES), "status": "dependency_policy_passed",
               "manuscript_completeness": "not_assessed_by_dependency_audit"}
    return [("KLT_TRUST_INVENTORY_BEGIN", begin)] + [("KLT_TRUST_DECL", d) for d in decls] + [
        ("KLT_TRUST_INVENTORY_END", {"declaration_count": len(decls)}), ("KLT_TRUST_AUDIT", summary)]


def encode(records):
    return "\n".join(tag + " " + json.dumps(value) for tag, value in records)


def admission(entries=None):
    return {"entries": entries if entries is not None else registry_entries()}


class InventoryTests(unittest.TestCase):
    def test_accepts_consistent_registry_and_inventory(self):
        result = P.parse_inventory(encode(fixture()), admission())
        self.assertEqual(len(result["mathematical"]), 1 + len(P.LITERATURE_NAMES))
        self.assertEqual(len(P.LITERATURE_NAMES), 28)

    def test_literature_header_must_list_exactly_the_registry(self):
        rows = fixture()
        rows[0][1]["literature_axioms"] = rows[0][1]["literature_axioms"][:-1]
        with self.assertRaises(P.ValidationError):
            P.parse_inventory(encode(rows), admission())
        entries = registry_entries()[:-1]
        with self.assertRaises(P.ValidationError):
            P.parse_inventory(encode(fixture()), admission(entries))

    def test_forbidden_transitive_axiom_rejected(self):
        bad = declaration("KltDP.Synthetic.usesNative")
        bad["closure"]["transitive_axioms"] = ["Lean.ofReduceBool"]
        with self.assertRaisesRegex(P.ValidationError, "Forbidden transitive axiom"):
            P.parse_inventory(encode(fixture([bad])), admission())
        unlisted = declaration("KltDP.Synthetic.usesUnregistered")
        unlisted["closure"]["transitive_axioms"] = ["KltDP.Literature.Unregistered.literal"]
        with self.assertRaisesRegex(P.ValidationError, "Forbidden transitive axiom"):
            P.parse_inventory(encode(fixture([unlisted])), admission())

    def test_registered_axiom_type_hashes_are_checked(self):
        for field in ("type_expression_sha256", "printed_type_sha256"):
            entries = registry_entries()
            entries[5][field] = sha(b"tampered")
            with self.assertRaisesRegex(P.ValidationError, "differs from the registered type hash"):
                P.parse_inventory(encode(fixture()), admission(entries))

    def test_registered_axiom_row_identity_is_checked(self):
        rows = fixture()
        target = P.LITERATURE_NAMES[3]
        for change in ({"module": "KltDP.Somewhere.Else"}, {"kind": "definition", "reducibility_hints": "regular"},
                       {"unsafe": True}, {"source_range_present": False}, {"universe_parameters": ["u", "v"]},
                       {"scope": "unsafe_implementation", "root_policy_passes": None}):
            bad = copy.deepcopy(rows)
            for tag, value in bad:
                if tag == "KLT_TRUST_DECL" and value["name"] == target:
                    value.update(change)
            with self.assertRaises(P.ValidationError):
                P.parse_inventory(encode(bad), admission())
        missing = [row for row in rows if not (row[0] == "KLT_TRUST_DECL" and row[1]["name"] == target)]
        missing[0][1]["declaration_count"] -= 1
        missing[-2][1]["declaration_count"] -= 1
        missing[-1][1]["mathematical_declaration_count"] -= 1
        missing[-1][1]["transitive_axioms"] = [a for a in missing[-1][1]["transitive_axioms"] if a != target]
        with self.assertRaisesRegex(P.ValidationError, "exactly once"):
            P.parse_inventory(encode(missing), admission())


class RegistryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="klt-v7-registry-SYNTHETIC-")
        self.addCleanup(temporary.cleanup)
        self.project = Path(temporary.name)
        self.files = {}
        for name in P.LITERATURE_NAMES:
            path = self.project / P.source_path(name)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(source_bytes(name))
            self.files[P.source_path(name)] = source_bytes(name)
        for name, (path, digest) in P.HISTORICAL_REGISTRIES.items():
            original = HISTORICAL_ROOT / path
            if original.is_file():
                (self.project / path).parent.mkdir(parents=True, exist_ok=True)
                (self.project / path).write_bytes(original.read_bytes())
        self.write_registry(registry())

    def write_registry(self, value):
        data = (json.dumps(value, indent=2) + "\n").encode()
        (self.project / P.LITERATURE_REGISTRY).parent.mkdir(parents=True, exist_ok=True)
        (self.project / P.LITERATURE_REGISTRY).write_bytes(data)
        self.files[P.LITERATURE_REGISTRY] = data

    def record(self, overrides=None):
        files = {name: {"bytes": len(data), "sha256": sha(data)} for name, data in self.files.items()}
        files.update(overrides or {})
        sources = {name: info["sha256"] for name, info in files.items() if P.is_source(name)}
        return {"sources": sources, "inputs": {"files": files}, "outputs": {"files": copy.deepcopy(files)}}

    def validate(self, library=None, audit=None):
        return P.validate_literature_admission(library or self.record(), audit or self.record(), self.project)

    def test_accepts_consistent_registry(self):
        result = self.validate()
        self.assertEqual([entry["name"] for entry in result["entries"]], P.LITERATURE_NAMES)
        contract = result["source_report_contract"]
        self.assertEqual(contract["registry_sha256"], sha(self.files[P.LITERATURE_REGISTRY]))
        self.assertEqual(len(contract["files"]), 28)
        history = result["public_evidence"]["historical_registries"]
        self.assertEqual({row["name"] for row in history}, set(P.HISTORICAL_REGISTRIES))

    def test_registry_must_be_bound_in_both_snapshots(self):
        library = self.record()
        del library["outputs"]["files"][P.LITERATURE_REGISTRY]
        with self.assertRaises(P.ValidationError):
            self.validate(library=library)
        audit = self.record({P.LITERATURE_REGISTRY: {"bytes": 1, "sha256": sha(b"x")}})
        with self.assertRaises(P.ValidationError):
            self.validate(audit=audit)

    def test_registry_policy_schema_and_order(self):
        for change in ({"policy": "lean419_logical_boundary_four_stacks_v6"}, {"schema": "other"},
                       {"ordinary_axioms": ["propext", "Classical.choice"]}):
            self.write_registry({**registry(), **change})
            with self.assertRaises(P.ValidationError):
                self.validate()
        entries = registry_entries()
        entries[0], entries[1] = entries[1], entries[0]
        self.write_registry(registry(entries))
        with self.assertRaises(P.ValidationError):
            self.validate()

    def test_entry_module_path_and_hashes(self):
        for index, change in ((7, {"module": "KltDP.Literature.Wrong"}),
                              (7, {"source_path": "KltDP/Literature/Wrong.lean"}),
                              (7, {"source_sha256": sha(b"other")}),
                              (7, {"published_source": {}}),
                              (7, {"extra": True}),
                              (0, {"original_registry": {"path": "audit/other.json", "sha256": sha(b"x")}})):
            entries = registry_entries()
            entries[index].update(change)
            self.write_registry(registry(entries))
            with self.assertRaises(P.ValidationError):
                self.validate()

    def test_historical_pointer_required_only_for_the_four(self):
        entries = registry_entries()
        target = next(entry for entry in entries if entry["name"] == "KltDP.Literature.Stacks.field_isJ2")
        del target["original_registry"]
        self.write_registry(registry(entries))
        with self.assertRaisesRegex(P.ValidationError, "Historical registry pointer"):
            self.validate()
        entries = registry_entries()
        entries[0]["original_registry"] = {"path": "audit/x.json", "sha256": sha(b"x")}
        self.write_registry(registry(entries))
        with self.assertRaisesRegex(P.ValidationError, "Unexpected historical registry pointer"):
            self.validate()

    def test_historical_registry_file_is_rehashed_when_present(self):
        path, _ = P.HISTORICAL_REGISTRIES["KltDP.Literature.Stacks.field_isJ2"]
        if not (self.project / path).is_file():
            self.skipTest("historical registry not available beside this test")
        (self.project / path).write_bytes(b"{}\n")
        with self.assertRaisesRegex(P.ValidationError, "Historical registry file differs"):
            self.validate()

    def test_local_source_and_snapshot_source_must_agree(self):
        target = P.source_path(P.LITERATURE_NAMES[9])
        (self.project / target).write_bytes(b"axiom changed : True\n")
        with self.assertRaisesRegex(P.ValidationError, "differs locally"):
            self.validate()
        (self.project / target).write_bytes(self.files[target])
        library = self.record({target: {"bytes": 1, "sha256": sha(b"other")}})
        with self.assertRaisesRegex(P.ValidationError, "compiled snapshot"):
            self.validate(library=library)


REJECTION_LINE = "audit/CompiledTrust.lean:8:0: error: KLT trust audit rejected {n} mathematical declarations; inspect KLT_TRUST_FAILURE records"
ROOT = "KltDP.Synthetic.mainTheorem"
COMPANION = "_private.KltDP.Synthetic.Meta.0.KltDP.Synthetic.Meta.headZeta._unsafe_rec"
OWNER = "_private.KltDP.Synthetic.Meta.0.KltDP.Synthetic.Meta.headZeta"


def companion_rows(name=COMPANION, module="KltDP.Synthetic.Meta"):
    """The exact shape Lean 4.19 gives a source-level `partial def`: opaque wrapper + partial companion."""
    owner = declaration(name[:-len(P.UNSAFE_REC_SUFFIX)])
    owner.update(module=module, kind="opaque", reducibility_hints=None)
    row = declaration(name)
    row.update(module=module, partial=True, root_policy_passes=False, source_range_present=False)
    row["closure"].update(passes=False, partial_dependencies=[name])
    return owner, row


def itemize_fixture(extra_rows=(), root_dependencies=(), failures=None, with_companion=True):
    root = declaration(ROOT)
    root.update(kind="theorem", reducibility_hints=None, direct_dependencies=list(root_dependencies))
    owner, companion = companion_rows()
    decls = [declaration(), root] + ([owner, companion] if with_companion else []) + list(extra_rows) + \
        [axiom_row(name) for name in P.LITERATURE_NAMES]
    failures = ([companion] if with_companion else []) if failures is None else failures
    mathematical = [d for d in decls if d["scope"] == "mathematical_declaration"]
    axioms = sorted({a for d in mathematical for a in d["closure"]["transitive_axioms"]})
    begin = {"schema": P.SCHEMA, "compiler_cache_policy": P.CACHE_POLICY,
             "foundational_axioms": sorted(P.FOUNDATIONS), "literature_axioms": list(P.LITERATURE_NAMES),
             "declaration_count": len(decls), "scope": "SYNTHETIC parser regression only"}
    summary = {"schema": P.SCHEMA, "compiler_cache_policy": P.CACHE_POLICY,
               "mathematical_declaration_count": len(mathematical), "runtime_companion_count": 0,
               "compiler_stage_cache_count": 0, "unsafe_implementation_count": 0,
               "failed_declaration_count": len(failures), "transitive_axioms": axioms,
               "literature_axioms": list(P.LITERATURE_NAMES),
               "status": "dependency_policy_failed" if failures else "dependency_policy_passed",
               "manuscript_completeness": "not_assessed_by_dependency_audit"}
    return ([("KLT_TRUST_INVENTORY_BEGIN", begin)] + [("KLT_TRUST_DECL", d) for d in decls] +
            [("KLT_TRUST_INVENTORY_END", {"declaration_count": len(decls)})] +
            [("KLT_TRUST_FAILURE", {"name": f["name"], "closure": f["closure"]}) for f in failures] +
            [("KLT_TRUST_AUDIT", summary)])


def encode_failed(records, n=None, extra_lines=()):
    text = encode(records)
    failures = sum(1 for tag, _ in records if tag == "KLT_TRUST_FAILURE")
    lines = list(extra_lines)
    if failures or n is not None:
        lines.append(REJECTION_LINE.format(n=failures if n is None else n))
    return text + ("\n" + "\n".join(lines) if lines else "")


def itemize(exit_code="1", roots=(ROOT,)):
    return {"roots": list(roots), "exit_code": exit_code}


class ItemizeInventoryTests(unittest.TestCase):
    def test_strict_mode_still_refuses_any_failure(self):
        with self.assertRaisesRegex(P.ValidationError, "trust rejection message"):
            P.parse_inventory(encode_failed(itemize_fixture()), admission())
        with self.assertRaisesRegex(P.ValidationError, "Audit emitted KLT_TRUST_FAILURE"):
            P.parse_inventory(encode(itemize_fixture()), admission())

    def test_companion_failure_outside_root_closure_is_itemized(self):
        result = P.parse_inventory(encode_failed(itemize_fixture()), admission(), itemize())
        itemized = result["itemized_nonroot_failures"]
        self.assertEqual([row["name"] for row in itemized["failures"]], [COMPANION])
        self.assertEqual(itemized["failures"][0]["owner"], OWNER)
        self.assertEqual(itemized["failure_modules"], ["KltDP.Synthetic.Meta"])
        self.assertEqual(itemized["roots"][0]["name"], ROOT)
        self.assertEqual(itemized["roots"][0]["reachable_project_declarations"], 1)
        self.assertEqual(result["summary"]["failed_declaration_count"], 1)
        # The failing companion is a mathematical root in the auditor's count.
        self.assertIn(COMPANION, [d["name"] for d in result["mathematical"]])

    def test_zero_failures_in_itemize_mode_require_clean_exit(self):
        records = itemize_fixture(failures=[])
        # The companion row still says it failed, so the inventory itself is inconsistent.
        with self.assertRaises(P.ValidationError):
            P.parse_inventory(encode_failed(records), admission(), itemize("0"))
        clean = itemize_fixture(with_companion=False)
        result = P.parse_inventory(encode(clean), admission(), itemize("0"))
        self.assertEqual(result["itemized_nonroot_failures"]["failure_count"], 0)
        with self.assertRaisesRegex(P.ValidationError, "exit zero"):
            P.parse_inventory(encode(clean), admission(), itemize("1"))

    def test_exit_status_and_rejection_message_must_match_failures(self):
        records = itemize_fixture()
        with self.assertRaisesRegex(P.ValidationError, "status 1"):
            P.parse_inventory(encode_failed(records), admission(), itemize("0"))
        with self.assertRaisesRegex(P.ValidationError, "status 1"):
            P.parse_inventory(encode_failed(records, n=2), admission(), itemize())
        with self.assertRaisesRegex(P.ValidationError, "status 1"):
            P.parse_inventory(encode(records), admission(), itemize())
        with self.assertRaisesRegex(P.ValidationError, "Lean errors other than"):
            P.parse_inventory(encode_failed(records, extra_lines=["KltDP/X.lean:3:1: error: unknown identifier"]),
                              admission(), itemize())

    def test_root_reaching_companion_is_refused_by_both_checks(self):
        # Closure data honest: root lists the companion as a partial dependency.
        records = itemize_fixture(root_dependencies=[COMPANION])
        for tag, row in records:
            if tag == "KLT_TRUST_DECL" and row["name"] == ROOT:
                row["root_policy_passes"] = False
                row["closure"].update(passes=False, partial_dependencies=[COMPANION])
        records[-1][1]["failed_declaration_count"] = 2
        records.insert(-1, ("KLT_TRUST_FAILURE", {"name": ROOT, "closure": next(
            row["closure"] for tag, row in records if tag == "KLT_TRUST_DECL" and row["name"] == ROOT)}))
        with self.assertRaisesRegex(P.ValidationError, "not a partial-definition companion"):
            P.parse_inventory(encode_failed(records), admission(), itemize())
        # Closure data claims the root is clean while its exported edges reach the companion.
        records = itemize_fixture(root_dependencies=[COMPANION])
        with self.assertRaisesRegex(P.ValidationError, "reaches an itemized failure"):
            P.parse_inventory(encode_failed(records), admission(), itemize())
        # Indirect path through an intermediate project declaration.
        middle = declaration("KltDP.Synthetic.middle")
        middle["direct_dependencies"] = [OWNER, COMPANION]
        records = itemize_fixture(extra_rows=[middle], root_dependencies=["KltDP.Synthetic.middle"])
        with self.assertRaisesRegex(P.ValidationError, "reaches an itemized failure"):
            P.parse_inventory(encode_failed(records), admission(), itemize())
        # Reaching only the passing opaque wrapper is fine.
        middle["direct_dependencies"] = [OWNER]
        records = itemize_fixture(extra_rows=[middle], root_dependencies=["KltDP.Synthetic.middle"])
        result = P.parse_inventory(encode_failed(records), admission(), itemize())
        self.assertEqual(result["itemized_nonroot_failures"]["roots"][0]["reachable_project_declarations"], 3)
        self.assertEqual(result["itemized_nonroot_failures"]["roots"][0]["reachable_declarations_in_failure_modules"], [OWNER])

    def test_non_companion_failures_are_refused(self):
        # A failing axiom root (forbidden axiom) is not a companion.
        oracle = declaration("KltDP.Synthetic.oracle")
        oracle.update(kind="axiom", reducibility_hints=None, root_policy_passes=False)
        oracle["closure"].update(passes=False, transitive_axioms=["KltDP.Synthetic.oracle"],
                                 forbidden_axioms=["KltDP.Synthetic.oracle"])
        records = itemize_fixture(extra_rows=[oracle])
        records[-1][1]["failed_declaration_count"] = 2
        records[-1][1]["transitive_axioms"] = sorted(set(records[-1][1]["transitive_axioms"]) | {"KltDP.Synthetic.oracle"})
        records.insert(-1, ("KLT_TRUST_FAILURE", {"name": oracle["name"], "closure": oracle["closure"]}))
        with self.assertRaisesRegex(P.ValidationError, "not a partial-definition companion"):
            P.parse_inventory(encode_failed(records), admission(), itemize())
        # A companion whose owner is missing, or is not an opaque wrapper, or lives elsewhere.
        for change in ("drop_owner", "owner_kind", "owner_module", "owner_fails"):
            records = itemize_fixture()
            for index, (tag, row) in enumerate(list(records)):
                if tag == "KLT_TRUST_DECL" and row["name"] == OWNER:
                    if change == "drop_owner":
                        del records[index]
                        records[0][1]["declaration_count"] -= 1
                        next(row for tag, row in records if tag == "KLT_TRUST_INVENTORY_END")["declaration_count"] -= 1
                        records[-1][1]["mathematical_declaration_count"] -= 1
                    elif change == "owner_kind":
                        row.update(kind="definition", reducibility_hints="regular")
                    elif change == "owner_module":
                        row["module"] = "KltDP.Synthetic.Elsewhere"
                    else:
                        row["root_policy_passes"] = False
                        row["closure"].update(passes=False, unsafe_dependencies=["x"])
            with self.assertRaises(P.ValidationError):
                P.parse_inventory(encode_failed(records), admission(), itemize())
        # A companion that also has a non-partial failure cause, or a partial dependency outside the set.
        for key, value in (("unsafe_dependencies", ["KltDP.Synthetic.evil"]),
                           ("forbidden_axioms", ["sorryAx"]),
                           ("missing_checked_declarations", ["gone"]),
                           ("partial_dependencies", [COMPANION, "KltDP.Synthetic.otherPartial"])):
            records = itemize_fixture()
            for tag, row in records:
                if tag in {"KLT_TRUST_DECL", "KLT_TRUST_FAILURE"} and row["name"] == COMPANION:
                    row["closure"][key] = value
                    if key == "forbidden_axioms":
                        row["closure"]["transitive_axioms"] = ["sorryAx"]
            if key == "forbidden_axioms":
                records[-1][1]["transitive_axioms"] = sorted(set(records[-1][1]["transitive_axioms"]) | {"sorryAx"})
            with self.assertRaises(P.ValidationError):
                P.parse_inventory(encode_failed(records), admission(), itemize())
        # Failure record whose closure differs from the declaration row.
        records = itemize_fixture()
        records[-2][1]["closure"] = dict(records[-2][1]["closure"], transitive_dependency_count_including_root=99)
        with self.assertRaisesRegex(P.ValidationError, "differs from the declaration"):
            P.parse_inventory(encode_failed(records), admission(), itemize())
        # A root that does not pass cannot be listed; an unknown root cannot be listed.
        with self.assertRaisesRegex(P.ValidationError, "absent from the inventory"):
            P.parse_inventory(encode_failed(itemize_fixture()), admission(), itemize(roots=("KltDP.Synthetic.nowhere",)))
        with self.assertRaisesRegex(P.ValidationError, "does not pass the policy"):
            P.parse_inventory(encode_failed(itemize_fixture()), admission(), itemize(roots=(COMPANION,)))


class ItemizeSourceGateTests(unittest.TestCase):
    """Run the real v7 linter on a synthetic tree and replay it through the parser's source gate."""

    LINTER = ROOT_DIR = None

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="klt-v7-source-gate-SYNTHETIC-")
        self.addCleanup(temporary.cleanup)
        self.project = Path(temporary.name)
        self.linter = Path(__file__).resolve().parent / "audit_sources.py"
        self.assertEqual(sha(self.linter.read_bytes()), P.SOURCE_LINTER_SHA256,
                         "test must run beside the reviewed v7 linter")
        (self.project / "scripts").mkdir()
        (self.project / "scripts/audit_sources.py").write_bytes(self.linter.read_bytes())
        (self.project / "KltDP/Audit").mkdir(parents=True)
        (self.project / "KltDP/Audit/Trust.lean").write_text("import Lean\npartial def tooling := tooling\n")
        for name in P.LITERATURE_NAMES:
            path = self.project / P.source_path(name)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(source_bytes(name))
        (self.project / "KltDP/Synthetic").mkdir(parents=True)
        self.meta = self.project / "KltDP/Synthetic/Meta.lean"
        self.meta.write_text("import Lean\nopen Lean Elab Term\n"
                             "private partial def headZeta (e : Expr) : Expr := headZeta e\n"
                             'elab "native%" : term => do throwError "unexpected {1}"\n')
        self.plain = self.project / "KltDP/Synthetic/Plain.lean"
        self.plain.write_text("import KltDP.Synthetic.Meta\n@[simps] def pair : Nat × Nat := (0, 0)\n"
                              "theorem checked : True := True.intro\n")
        modules = sorted(P.source_path(n)[:-5].replace("/", ".") for n in P.LITERATURE_NAMES) + \
            ["KltDP.Synthetic.Meta", "KltDP.Synthetic.Plain"]
        (self.project / "KltDP.lean").write_text("".join(f"import {m}\n" for m in modules))
        self.registry_bytes = None

    def run_linter(self):
        entries = []
        for name in P.LITERATURE_NAMES:
            path = P.source_path(name)
            entries.append({"name": name, "module": P.LITERATURE_MODULES[name], "source_path": path,
                            "source_sha256": sha((self.project / path).read_bytes()),
                            "universe_parameters": ["u"], "type_expression_sha256": sha(b"raw"),
                            "printed_type_sha256": sha(b"printed"), "published_source": {"reference": "SYNTHETIC"}})
        registry = {"schema": P.LITERATURE_REGISTRY_SCHEMA, "policy": P.CACHE_POLICY,
                    "ordinary_axioms": sorted(P.FOUNDATIONS), "active_literature_axioms": entries}
        (self.project / "audit").mkdir(exist_ok=True)
        self.registry_bytes = (json.dumps(registry, indent=1) + "\n").encode()
        (self.project / P.LITERATURE_REGISTRY).write_bytes(self.registry_bytes)
        import subprocess, sys
        result = subprocess.run([sys.executable, str(self.project / "scripts/audit_sources.py"), "--root", str(self.project),
                                 "--output", str(self.project / P.SOURCE_LINT_REPORT)], capture_output=True, text=True)
        self.assertIn(result.returncode, (0, 1), result.stderr)
        report = json.loads((self.project / P.SOURCE_LINT_REPORT).read_text())
        return report

    def records(self):
        files = {}
        for path in list((self.project / "KltDP").rglob("*.lean")) + [self.project / "KltDP.lean",
                self.project / P.SOURCE_LINTER, self.project / P.SOURCE_LINT_REPORT, self.project / P.LITERATURE_REGISTRY]:
            data = path.read_bytes()
            files[str(path.relative_to(self.project))] = {"bytes": len(data), "sha256": sha(data)}
        sources = {name: info["sha256"] for name, info in files.items() if P.is_source(name)}
        record = {"sources": sources, "inputs": {"files": files}, "outputs": {"files": copy.deepcopy(files)}}
        return record, copy.deepcopy(record)

    def admission(self):
        library, _ = self.records()
        files = [{"path": P.source_path(name), "name": name, "sha256": library["sources"][P.source_path(name)]}
                 for name in P.LITERATURE_NAMES]
        return {"entries": [], "source_report_contract": {"registry_path": P.LITERATURE_REGISTRY,
                                                          "registry_sha256": sha(self.registry_bytes), "files": files}}

    def test_elab_partial_rejections_and_reviews_are_itemized_only_in_itemize_mode(self):
        report = self.run_linter()
        self.assertEqual(report["status"], "source_lint_rejected")
        self.assertEqual(sorted(row["token"] for row in report["mathematical_source_rejections"]), ["elab", "partial"])
        library, audit = self.records()
        with self.assertRaisesRegex(P.ValidationError, "status/linter binding"):
            P.validate_source_lint(library, audit, self.project, self.admission(), itemize=False)
        result = P.validate_source_lint(library, audit, self.project, self.admission(), itemize=True)
        self.assertEqual(result["status"], "source_lint_rejected")
        itemized = result["itemized_findings"]
        self.assertEqual(itemized["rejection_count"], 2)
        self.assertEqual(itemized["rejection_files"], ["KltDP/Synthetic/Meta.lean"])
        self.assertEqual(sorted(row["token"] for row in itemized["rejections"]), ["elab", "partial"])
        self.assertGreaterEqual(itemized["review_count"], 2)
        self.assertIn("KltDP/Synthetic/Plain.lean", itemized["review_files"])
        self.assertEqual(result["reproduced_source_count"], 28 + 4)

    def test_other_rejections_and_import_rejections_still_refuse(self):
        self.plain.write_text("import KltDP.Synthetic.Meta\ntheorem bad : False := by sorry\n")
        self.run_linter()
        library, audit = self.records()
        with self.assertRaisesRegex(P.ValidationError, "cannot be itemized"):
            P.validate_source_lint(library, audit, self.project, self.admission(), itemize=True)
        self.plain.write_text("import KltDP.Synthetic.Meta\ntheorem checked : True := True.intro\n"
                              "theorem native : 2 + 2 = 4 := by native_decide\n")
        self.run_linter()
        library, audit = self.records()
        with self.assertRaisesRegex(P.ValidationError, "cannot be itemized"):
            P.validate_source_lint(library, audit, self.project, self.admission(), itemize=True)
        self.plain.write_text("import Unscanned.Attack\ntheorem checked : True := True.intro\n")
        self.run_linter()
        library, audit = self.records()
        with self.assertRaisesRegex(P.ValidationError, "import_policy_rejections"):
            P.validate_source_lint(library, audit, self.project, self.admission(), itemize=True)

    def test_recorded_arrays_must_reproduce_exactly(self):
        self.run_linter()
        report_path = self.project / P.SOURCE_LINT_REPORT
        report = json.loads(report_path.read_text())
        report["mathematical_source_rejections"] = report["mathematical_source_rejections"][:1]
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        library, audit = self.records()
        with self.assertRaises(P.ValidationError):
            P.validate_source_lint(library, audit, self.project, self.admission(), itemize=True)

class DeclarationFreeModuleTests(unittest.TestCase):
    """The completeness clause accepts an inventory-absent module only when its exact source declares nothing."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="klt-v7-declaration-free-SYNTHETIC-")
        self.addCleanup(temporary.cleanup)
        self.project = Path(temporary.name)
        linter_path = Path(__file__).resolve().parent / "audit_sources.py"
        self.assertEqual(sha(linter_path.read_bytes()), P.SOURCE_LINTER_SHA256,
                         "test must run beside the reviewed v7 linter")
        (self.project / "scripts").mkdir()
        (self.project / "scripts/audit_sources.py").write_bytes(linter_path.read_bytes())
        self.linter = P.reviewed_linter(self.project)
        (self.project / "KltDP/Synthetic").mkdir(parents=True)
        self.plain = self.write("Plain", "theorem checked : True := True.intro\n")

    def write(self, name, text):
        path = f"KltDP/Synthetic/{name}.lean"
        (self.project / path).write_text(text)
        return f"KltDP.Synthetic.{name}", path

    def completeness(self, files, represented, extra_rows=()):
        modules = dict(files)
        sources = {path: sha((self.project / path).read_bytes()) for path in modules.values()}
        rows = [{"module": name} for name in represented]
        inventory = {"mathematical": rows, "companions": [],
                     "declarations": rows + [{"module": name} for name in extra_rows]}
        return P.validate_module_completeness(self.project, sources, modules, inventory, self.linter)

    def test_scan_is_comment_and_docstring_aware(self):
        free = ("import KltDP.Synthetic.Plain\n\n/-! Exact public closures.\n"
                "theorem inside_a_docstring : False := sorry -- never code -/\n"
                "-- theorem in_a_line_comment : False := sorry\n"
                "#check KltDP.Synthetic.checked\n#print axioms KltDP.Synthetic.checked\n"
                "#check @KltDP.Synthetic.checked\n#print KltDP.Synthetic.checked\n")
        self.assertEqual(P.declaration_free_commands(free, self.linter), {"import": 1, "#check": 2, "#print": 2})
        self.assertEqual(P.declaration_free_commands("import KltDP.Synthetic.Plain\n\n/-! Supplied elsewhere. -/\n",
                                                     self.linter), {"import": 1})
        self.assertEqual(P.declaration_free_commands(
            "import Mathlib\nopen Foo Bar\nnamespace Baz\nsection\nuniverse u v\n"
            "variable {R : Type u} [CommRing R] (x : R)\nset_option autoImplicit false\nend\nend Baz\n",
            self.linter), {"import": 1, "open": 1, "namespace": 1, "section": 1, "universe": 1,
                           "variable": 1, "set_option": 1, "end": 2})
        for text in ("import KltDP.Synthetic.Plain\ntheorem extra : True := True.intro\n",
                     "import KltDP.Synthetic.Plain\nopen KltDP in theorem extra : True := True.intro\n",
                     "import KltDP.Synthetic.Plain\nopen KltDP in\n#check KltDP.Synthetic.checked\n",
                     "import KltDP.Synthetic.Plain\nexample : True := True.intro\n",
                     "import KltDP.Synthetic.Plain\n#check KltDP.Synthetic.checked\ninstance : Inhabited Nat := ⟨0⟩\n",
                     "import KltDP.Synthetic.Plain\n#eval 1\n",
                     "import KltDP.Synthetic.Plain\n#guard_msgs in\n#check KltDP.Synthetic.checked\n",
                     "import KltDP.Synthetic.Plain\n#check (fun n : Nat =>\n  n)\n",
                     "import KltDP.Synthetic.Plain\n#check KltDP.Synthetic.checked\n  KltDP.Synthetic.checked\n",
                     "import KltDP.Synthetic.Plain\n#print \"theorem\"\n",
                     "import KltDP.Synthetic.Plain\nattribute [simp] KltDP.Synthetic.checked\n",
                     "import KltDP.Synthetic.Plain\nset_option autoImplicit false in\ndef extra := 1\n",
                     "import KltDP.Synthetic.Plain\nvariable (x : Nat := 0)\n",
                     "import KltDP.Synthetic.Plain\nnoncomputable section\nend\n",
                     "import KltDP.Synthetic.Plain\nderiving instance Repr for Nat\n",
                     "import KltDP.Synthetic.Plain\nexport Nat (succ)\n",
                     "import KltDP.Synthetic.Plain\nmacro \"m\" : term => `(1)\n"):
            self.assertIsNone(P.declaration_free_commands(text, self.linter), text)

    def test_declaration_free_absent_modules_are_accepted_and_itemized(self):
        exports = self.write("Exports", "import KltDP.Synthetic.Plain\n\n#check KltDP.Synthetic.checked\n"
                                        "#print axioms KltDP.Synthetic.checked\n#check @KltDP.Synthetic.checked\n"
                                        "#print KltDP.Synthetic.checked\n")
        charts = self.write("Charts", "import KltDP.Synthetic.Plain\n\n/-! Supplied by the separately checked assembly.\n"
                                      "theorem inside_a_docstring : False := sorry -/\n")
        result = self.completeness([exports, charts, self.plain], [self.plain[0]])
        self.assertEqual(result["count"], 2)
        self.assertEqual([row["module"] for row in result["modules"]], [charts[0], exports[0]])
        rows = {row["module"]: row for row in result["modules"]}
        self.assertEqual(rows[exports[0]]["commands"], {"import": 1, "#check": 2, "#print": 2})
        self.assertEqual(rows[charts[0]]["commands"], {"import": 1})
        for name, path in (exports, charts):
            self.assertEqual(rows[name]["source"], path)
            self.assertEqual(rows[name]["sha256"], sha((self.project / path).read_bytes()))
        self.assertEqual(result["accepted_command_forms"], P.DECLARATION_FREE_FORMS)
        self.assertEqual(self.completeness([self.plain], [self.plain[0]])["modules"], [])

    def test_absent_module_with_a_declaration_is_still_refused(self):
        exports = self.write("Exports", "import KltDP.Synthetic.Plain\n#check KltDP.Synthetic.checked\n")
        for text in ("import KltDP.Synthetic.Plain\ntheorem extra : True := True.intro\n",
                     "import KltDP.Synthetic.Plain\n/-! doc -/\nopen KltDP in theorem extra : True := True.intro\n",
                     "import KltDP.Synthetic.Plain\n#check KltDP.Synthetic.checked\ndef extra := 1\n",
                     "import KltDP.Synthetic.Plain\n#guard_msgs in\n#check KltDP.Synthetic.checked\n"):
            extra = self.write("Extra", text)
            with self.assertRaisesRegex(P.ValidationError,
                                        "absent from inventory: KltDP.Synthetic.Extra$"):
                self.completeness([exports, extra, self.plain], [self.plain[0]])
        with self.assertRaisesRegex(P.ValidationError, "absent from inventory: KltDP.Synthetic.Extra$"):
            self.completeness([extra, self.plain], [self.plain[0]])

    def test_declaration_free_module_with_inventory_rows_or_changed_bytes_is_refused(self):
        exports = self.write("Exports", "import KltDP.Synthetic.Plain\n#check KltDP.Synthetic.checked\n")
        with self.assertRaisesRegex(P.ValidationError, "inventory rows: KltDP.Synthetic.Exports"):
            self.completeness([exports, self.plain], [self.plain[0]], extra_rows=[exports[0]])
        modules = dict([exports, self.plain])
        sources = {path: sha((self.project / path).read_bytes()) for path in modules.values()}
        sources[exports[1]] = sha(b"other bytes")
        inventory = {"mathematical": [{"module": self.plain[0]}], "companions": [],
                     "declarations": [{"module": self.plain[0]}]}
        with self.assertRaisesRegex(P.ValidationError, "changed locally"):
            P.validate_module_completeness(self.project, sources, modules, inventory, self.linter)

    def test_other_completeness_rules_are_unchanged(self):
        with self.assertRaisesRegex(P.ValidationError, "outside the archived source snapshot: KltDP.Elsewhere"):
            self.completeness([self.plain], [self.plain[0]], extra_rows=["KltDP.Elsewhere"])
        modules = dict([self.plain])
        sources = {path: sha((self.project / path).read_bytes()) for path in modules.values()}
        sources["KltDP/Synthetic/Ghost.lean"] = sha(b"")
        rows = [{"module": self.plain[0]}, {"module": "KltDP.Synthetic.Ghost"}]
        inventory = {"mathematical": rows, "companions": [], "declarations": rows}
        with self.assertRaisesRegex(P.ValidationError, "outside library snapshot: KltDP.Synthetic.Ghost"):
            P.validate_module_completeness(self.project, sources, modules, inventory, self.linter)


class ResourceProfileTests(unittest.TestCase):
    def test_profiles_and_roles(self):
        self.assertEqual(P.resource_caps("library", "memory256cpu4")["memory.max"], "274877906944")
        self.assertEqual(P.resource_caps("audit", "standard26")["memory.max"], "27917287424")
        for role, profile in (("probe", "standard26"), ("library", "dev128cpu16")):
            with self.assertRaises(P.ValidationError):
                P.resource_caps(role, profile)


if __name__ == "__main__":
    unittest.main()
