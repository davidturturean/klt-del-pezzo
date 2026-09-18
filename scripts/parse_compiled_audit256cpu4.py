#!/usr/bin/env python3
"""Validate archived VM build/trust records without executing Lean or Lake.

This certifies record consistency and the emitted dependency policy only. It
does not certify statement fidelity, inhabitance, or manuscript completion.
The complete parsed inventory is written beside --output as *.records.json.

Policy v7 (lean419_logical_boundary_twentyeight_admissions_v7): the literature
allowlist is the exact twenty-eight-entry registry audit/literature-assumptions.json,
which binds each admitted axiom's name, owning module, source hash and both type
hashes; the four historical Stacks registries are retained as history. Every other
record, closure, cache, source-gate and native-type check is unchanged from v6.

One scoped alternative mode exists, --itemize-nonroot-failures ROOT...: it emits a
certificate with status passed_with_itemized_nonroot_failures if and only if every
KLT_TRUST_FAILURE is a source-level `partial def` companion (`_unsafe_rec`, failing only
through its own partial safety) that lies outside the dependency closure of every listed
logical ROOT, and every source-lint rejection is an `elab`/`partial` token; all such
items are listed in the certificate. Any other failure or rejection keeps the refusal.
Without the flag the strict certificate is unchanged.

Module completeness: every library module must own at least one inventory row, except
that a module whose exact archived source is declaration-free (only import, open,
namespace, section, end, universe, variable, set_option, #check and #print lines, in their
one-line forms, after the reviewed linter masks comments, docstrings and strings) is
accepted and itemized under declaration_free_modules with its source hash. #eval,
#guard_msgs, every declaration and every `in` combinator keep the module subject to the
rule. This applies in both modes.

The canonical five-line #klt_trust_report driver is recognized byte-for-byte.
Historical separate-command drivers also require --driver-format-record: a
JSON object with schema "klt-audit-driver-format-v1", format
"separate_inventory_audit_v1", path "audit/CompiledTrust.lean", and the exact
driver's integer bytes count and sha256. Only the two reviewed legacy byte
templates are accepted; the record does not authorize another Lean program.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shlex
import sys
from collections.abc import Iterable, Iterator
from datetime import datetime, timedelta, timezone
from types import ModuleType


LEAN = "4.19.0"
DEPENDENCIES = {
    "mathlib": "c44e0c8ee63ca166450922a373c7409c5d26b00b",
    "plausible": "77e08eddc486491d7b9e470926b3dbe50319451a",
    "LeanSearchClient": "25078369972d295301f5a1e53c3e5850cf6d9d4c",
    "importGraph": "e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b",
    "proofwidgets": "c4919189477c3221e6a204008998b0d724f49904",
    "aesop": "5d50b08dedd7d69b3d9b3176e0d58a23af228884",
    "Qq": "fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02",
    "batteries": "f5d04a9c4973d401c8c92500711518f7c656f034",
    "Cli": "02dbd02bc00ec4916e99b04b2245b30200e200d0",
}
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}
CAPS = {"cpu.max": "400000 100000", "memory.max": "27917287424",
        "memory.swap.max": "0"}
CAPS256CPU4 = {"cpu.max": "400000 100000", "memory.max": "274877906944",
          "memory.swap.max": "0"}
CANONICAL_RESOURCE_PROFILES = ("standard26", "memory256cpu4")
TOOLING_SOURCE = "KltDP/Audit/Trust.lean"
TOOLING_MODULE = "KltDP.Audit.Trust"
AUDIT_DRIVER = "audit/CompiledTrust.lean"
DRIVER_FORMAT_SCHEMA = "klt-audit-driver-format-v1"
REPORT_DRIVER_FORMAT = "combined_report_v1"
LEGACY_DRIVER_FORMAT = "separate_inventory_audit_v1"
STREAM_REPORT_DRIVER_FORMAT = "combined_report_streaming_stderr_v1"
STREAM_TOOLING_SHA256 = "763c1464cb9261e033995594fa6524b8f8641af489aaf2f5daef3e8f904185e4"
NATIVE_REPORT_DRIVER_FORMAT = "combined_report_streaming_native_types_v2"
NATIVE_TOOLING_SHA256 = "c5f4646aaccc523bcdc4e626fd3387575c3260c1a867468a2b28665170e39bce"
NATIVE_TYPE_SCHEMA = "klt-compiled-trust-native-types-v2"
NATIVE_TYPE_ENCODING = "lean419-olean-constant-type-v1"
REPORT_DRIVER = (
    "import KltDP\n"
    "import KltDP.Audit.Trust\n"
    "set_option maxRecDepth 100000\n"
    "set_option maxHeartbeats 0\n"
    "#klt_trust_report\n"
).encode("utf-8")
STREAM_REPORT_DRIVER = (
    "import KltDP\n"
    "import KltDP.Audit.Trust\n"
    "set_option maxRecDepth 100000\n"
    "set_option maxHeartbeats 0\n"
    "set_option stderrAsMessages false\n"
    "set_option KltDP.Audit.Trust.streamOutput true\n"
    "#klt_trust_report\n"
).encode("utf-8")
NATIVE_REPORT_DRIVER = STREAM_REPORT_DRIVER.replace(
    b"#klt_trust_report\n",
    b"set_option KltDP.Audit.Trust.nativeTypeReferences true\n#klt_trust_report\n")
LEGACY_DRIVER = (
    "import KltDP\n"
    "import KltDP.Audit.Trust\n"
    "set_option maxRecDepth 100000\n"
    "set_option maxHeartbeats 0\n"
    "#klt_trust_inventory\n"
    "#klt_trust_audit\n"
).encode("utf-8")
LEGACY_GENERATED_DRIVER = (
    "-- Generated audit driver; generation is not compilation evidence.\n"
    "import KltDP\n"
    "import KltDP.Audit.Trust\n"
    "\n"
    "set_option maxRecDepth 100000\n"
    "set_option maxHeartbeats 0\n"
    "\n"
    "#klt_trust_inventory\n"
    "#klt_trust_audit\n"
).encode("utf-8")
SCHEMA = "klt-compiled-trust-v1"
CACHE_POLICY = "lean419_logical_boundary_twentyeight_admissions_v7"
SOURCE_LINTER = "scripts/audit_sources.py"
SOURCE_LINT_REPORT = "audit/source_lint.json"
# Reviewed literal/import/source gate for the v7 logical boundary (28-file axiom allowlist).
# Changing this digest requires review of the new script, not merely a rehash.
SOURCE_LINTER_SHA256 = "011042a01c2e6389ed4182c6917db345e4a68b1889c5cde8806548800f6c9af3"
LITERATURE_REGISTRY = "audit/literature-assumptions.json"
LITERATURE_REGISTRY_SCHEMA = "klt-literature-assumptions-v7"
# The twenty-eight literature admissions of policy v7 in canonical (lexicographic) name order,
# each with the module that must own the axiom; the source path is that module's file. Policy
# v6 admitted only the four Stacks entries listed in HISTORICAL_REGISTRIES, whose original
# registries are retained as history and rehashed when present.
LITERATURE_ADMISSIONS = (
    ("KltDP.Literature.Hartshorne.castelnuovo_contraction_literal",
     "KltDP.Literature.HartshorneCastelnuovoLiteral"),
    ("KltDP.Literature.Hartshorne.hasContractionLifts_instance",
     "KltDP.Literature.Hartshorne.StrictTransformInstance"),
    ("KltDP.Literature.Hartshorne.hurwitz_degreeTwo_projectiveLine_instance",
     "KltDP.Literature.Hartshorne.HurwitzDegreeTwoInstance"),
    ("KltDP.Literature.Hartshorne.integral_numerical_group_free_finite_literal",
     "KltDP.Literature.Hartshorne.IntegralNumericalGroup"),
    ("KltDP.Literature.Hartshorne.minimal_surface_classification_literal",
     "KltDP.Literature.Hartshorne.MinimalSurfaceClassification"),
    ("KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal",
     "KltDP.Literature.Hartshorne.SurfaceProjectivity"),
    ("KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal",
     "KltDP.Literature.Hartshorne.PointBlowupCohomology"),
    ("KltDP.Literature.Hartshorne.ruled_surface_genus_literal",
     "KltDP.Literature.Hartshorne.RuledSurfaceGenus"),
    ("KltDP.Literature.Hartshorne.ruled_surface_picard_literal",
     "KltDP.Literature.Hartshorne.RuledSurfacePicard"),
    ("KltDP.Literature.Hartshorne.surface_hodge_index_literal",
     "KltDP.Literature.Hartshorne.SurfaceHodgeIndex"),
    ("KltDP.Literature.Hartshorne.surface_nakai_moishezon_literal",
     "KltDP.Literature.Hartshorne.SurfaceNakaiMoishezon"),
    ("KltDP.Literature.Hartshorne.surface_riemannRoch_literal",
     "KltDP.Literature.Hartshorne.SurfaceRiemannRoch"),
    ("KltDP.Literature.Keel.semiampleness_completeSystem_literal",
     "KltDP.Literature.KeelCompleteSystem"),
    ("KltDP.Literature.Stacks.affine_morphism_cohomology_literal",
     "KltDP.Literature.Stacks.AffineMorphismCohomology"),
    ("KltDP.Literature.Stacks.blowupRegularPoint_literal",
     "KltDP.Literature.Stacks.BlowupRegularPointAdmitted"),
    ("KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal",
     "KltDP.Literature.StacksPointBlowupDomination"),
    ("KltDP.Literature.Stacks.field_isJ2",
     "KltDP.Literature.Stacks.FieldJ2"),
    ("KltDP.Literature.Stacks.lipman_resolution_of_normal_completions_literal",
     "KltDP.Literature.LipmanResolutionLiteral"),
    ("KltDP.Literature.Stacks.properCohomology_finite",
     "KltDP.Literature.Stacks.ProperCohomologyFinite"),
    ("KltDP.Literature.Stacks.properFlat_fiberEuler_literal",
     "KltDP.Literature.Stacks.ProperFlatFiberEuler"),
    ("KltDP.Literature.Stacks.proper_curve_pullback_degree_literal",
     "KltDP.Literature.ProperCurvePullbackDegreeLiteral"),
    ("KltDP.Literature.Stacks.proper_curve_tensor_degree_literal",
     "KltDP.Literature.Stacks.CurveTensorDegreeLiteral"),
    ("KltDP.Literature.Stacks.regularLocal_isUFD",
     "KltDP.Literature.Stacks.RegularLocalUFD"),
    ("KltDP.Literature.Stacks.regular_smooth_loci_perfect_literal",
     "KltDP.Literature.RegularSmoothLociLiteral"),
    ("KltDP.Literature.Stacks.smooth_standardSmooth_cover_literal",
     "KltDP.Literature.SmoothStandardCoverLiteral"),
    ("KltDP.Literature.Stacks.steinFactorization_noetherian_literal",
     "KltDP.Literature.SteinFactorizationNoetherian"),
    ("KltDP.Literature.Tanaka.contraction_44_instance",
     "KltDP.Literature.Tanaka.ContractionTheorem"),
    ("KltDP.Literature.Zariski.closedPoint_normal_completion_literal",
     "KltDP.Literature.ZariskiNormalCompletion"),
)
LITERATURE_MODULES = dict(LITERATURE_ADMISSIONS)
LITERATURE_NAMES = [name for name, _ in LITERATURE_ADMISSIONS]
HISTORICAL_REGISTRIES = {
    "KltDP.Literature.Stacks.field_isJ2":
        ("audit/field_j2_admission.json", "b341fef779503eac029e5543911d27851c7d12c829c28a0bc2707f61e724d997"),
    "KltDP.Literature.Stacks.regularLocal_isUFD":
        ("audit/regular_local_ufd_admission.json", "258ffdd90ad110c7d58572908c547e2f28efc4e3d5172597efe080df907e92ba"),
    "KltDP.Literature.Stacks.properCohomology_finite":
        ("audit/proper_cohomology_admission.json", "0639cd7244af87b8b102eab28a43916650207b7b9c8ad8d563c2ad81aea20dde"),
    "KltDP.Literature.Stacks.proper_curve_tensor_degree_literal":
        ("audit/curve_tensor_degree_admission.json", "436db9c3a61f6db0f9adc818ade10cd7abae36d1f11b62be4764e65228f0e635"),
}
REGISTRY_ENTRY_KEYS = {"name", "module", "source_path", "source_sha256", "universe_parameters",
                       "type_expression_sha256", "printed_type_sha256", "published_source"}
DECLARATION_KINDS = {"axiom", "definition", "theorem", "opaque", "quotient_primitive",
                     "inductive", "constructor", "recursor"}
TAGS = {"KLT_TRUST_INVENTORY_BEGIN", "KLT_TRUST_DECL",
        "KLT_TRUST_INVENTORY_END", "KLT_TRUST_AUDIT", "KLT_TRUST_FAILURE"}
ITEMIZED_STATUS = "passed_with_itemized_nonroot_failures"
ITEMIZED_SOURCE_TOKENS = {"elab", "partial"}
UNSAFE_REC_SUFFIX = "._unsafe_rec"
# The exact rejection message of KltDP.Audit.Trust.process, as printed by `lean` for the driver.
REJECTION_MESSAGE = re.compile(r"^(?:\./)*" + re.escape(AUDIT_DRIVER) +
                               r":\d+:\d+: error: KLT trust audit rejected (\d+) mathematical declarations; "
                               r"inspect KLT_TRUST_FAILURE records\s*$")
RECORD_FILES = ("inputs.json", "outputs.json", "cgroup.json", "build.log",
                "command.sh", "exit_code.txt", "started_at.txt", "completed_at.txt",
                "project.txt")


class ValidationError(ValueError):
    """Missing, inconsistent, truncated, or policy-rejected evidence."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON object key: {key}")
        result[key] = value
    return result


def reviewed_linter(project: Path, data: bytes | None = None) -> ModuleType:
    """Load the reviewed source gate from hash-checked bytes.

    Loading is safe only because the bytes match the reviewed constant. The compiled
    bytes are executed directly: Python import loaders may otherwise execute a
    timestamp-valid .pyc that was never reviewed. The __main__ entry point is not
    invoked and no report is written.
    """
    if data is None:
        data = (project / SOURCE_LINTER).read_bytes()
    require(sha256(data) == SOURCE_LINTER_SHA256, "Source-gate implementation differs from the reviewed linter")
    linter = ModuleType("_klt_reviewed_source_gate")
    linter.__file__ = str(project / SOURCE_LINTER)
    exec(compile(data, linter.__file__, "exec"), linter.__dict__)
    require(linter.SOURCE_POLICY_PROFILE == CACHE_POLICY, "Reviewed source-gate profile differs")
    return linter


# A library module with no inventory row is accepted only when its exact archived source,
# after the reviewed linter masks comments, docstrings and strings, consists solely of these
# one-line command forms (ASCII identifiers; a single optionally @-prefixed identifier as the
# #check/#print argument; no `in` combinators). Such a module declares nothing, so the compiled
# trust report legitimately has no row for it. Anything else leaves the module subject to the
# unchanged completeness rule. This is a conservative line-form check, not a Lean parser.
_IDENT = r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*"
DECLARATION_FREE_FORMS = {
    "import": rf"import(?:[ \t]+{_IDENT})+",
    "open": rf"open(?:[ \t]+{_IDENT})+",
    "namespace": rf"namespace[ \t]+{_IDENT}",
    "section": rf"section(?:[ \t]+{_IDENT})?",
    "end": rf"end(?:[ \t]+{_IDENT})?",
    "universe": rf"universe(?:[ \t]+{_IDENT})+",
    "variable": r"variable(?:[ \t]+[(\[{][^()\[\]{}:=]*(?::[^()\[\]{}:=]*)?[)\]}])+",
    "set_option": rf"set_option[ \t]+{_IDENT}[ \t]+(?:{_IDENT}|[0-9]+)",
    "#check": rf"#check[ \t]+@?{_IDENT}",
    "#print": rf"#print[ \t]+(?:axioms[ \t]+)?{_IDENT}",
}
# Command, declaration and combinator keywords that must not occur anywhere in the masked
# code of a declaration-free module; redundant with the line forms, and `in` also excludes
# the `open ... in` / `set_option ... in` command combinators.
DECLARATION_KEYWORDS = frozenset({
    "theorem", "lemma", "def", "abbrev", "instance", "example", "axiom", "structure", "class",
    "inductive", "opaque", "constant", "macro", "macro_rules", "syntax", "elab", "elab_rules",
    "notation", "infix", "infixl", "infixr", "prefix", "postfix", "declare_syntax_cat", "attribute",
    "noncomputable", "private", "protected", "partial", "unsafe", "mutual", "deriving", "initialize",
    "builtin_initialize", "run_cmd", "run_tac", "alias", "export", "add_decl_doc", "register_option",
    "local", "scoped", "in", "where", "let", "have", "fun", "match", "do", "by", "sorry", "omit", "include",
})


def declaration_free_commands(source: str, linter: ModuleType) -> dict[str, int] | None:
    """Count the command forms of a declaration-free source; None if any other code is present.

    Comments, docstrings and strings are masked with the reviewed linter's lexer, so a
    declaration keyword inside a docstring does not count and a masked string never hides
    code. Any line outside DECLARATION_FREE_FORMS, or any DECLARATION_KEYWORDS token in the
    masked code, makes the module ineligible.
    """
    masked = linter.mask_noncode(source)
    for token in re.finditer(r"[A-Za-z_][A-Za-z0-9_'!?.]*", masked):
        if token.group() in DECLARATION_KEYWORDS:
            return None
    counts: dict[str, int] = {}
    for line in masked.split("\n"):
        text = line.strip()
        if not text:
            continue
        for command, form in DECLARATION_FREE_FORMS.items():
            if re.fullmatch(form, text):
                counts[command] = counts.get(command, 0) + 1
                break
        else:
            return None
    return counts


def validate_module_completeness(project: Path, sources: dict[str, str], modules: dict[str, str],
                                 inventory: dict, linter: ModuleType) -> dict:
    """Every library module needs an inventory row unless its exact source is declaration-free.

    ``modules`` maps each library module to its archived source path and ``sources`` holds
    the archived hashes. A module with no mathematical or companion row is accepted only if
    declaration_free_commands accepts its source and no inventory row of any scope names it;
    such modules are itemized with their source hashes. Every other module stays subject to
    the unchanged completeness rule, and the inventory may not name modules outside the
    archived snapshot or the library.
    """
    represented = {d["module"] for d in inventory["mathematical"] + inventory["companions"]}
    all_inventory_modules = {d["module"] for d in inventory["declarations"]}
    archived_modules = {name[:-5].replace("/", ".") for name in sources}
    require(all_inventory_modules <= archived_modules,
            "Inventory contains declaration modules outside the archived source snapshot: " +
            ", ".join(sorted(all_inventory_modules - archived_modules)))
    declaration_free, absent = [], []
    for name in sorted(set(modules) - represented):
        path = modules[name]
        data = (project / path).read_bytes()
        require(sha256(data) == sources[path], f"Audited source changed locally: {path}")
        commands = declaration_free_commands(data.decode("utf-8"), linter)
        if commands is None:
            absent.append(name)
            continue
        require(name not in all_inventory_modules, f"Declaration-free source has inventory rows: {name}")
        declaration_free.append({"module": name, "source": path, "sha256": sources[path], "commands": commands})
    require(not absent, "Library mathematical modules absent from inventory: " + ", ".join(absent))
    require(represented <= set(modules) | {"KltDP"},
            "Inventory contains modules outside library snapshot: " + ", ".join(sorted(represented - set(modules) - {"KltDP"})))
    return {"count": len(declaration_free), "modules": declaration_free,
            "accepted_command_forms": dict(DECLARATION_FREE_FORMS),
            "scope": "Library modules with no inventory row whose exact archived source, after the reviewed linter "
                     "masks comments, docstrings and strings, consists only of the listed one-line command forms; "
                     "they declare nothing and are listed here, not exempted from any other check"}


def loads(data: str) -> object:
    return json.loads(data, object_pairs_hook=unique_object)


def artifact(path: Path) -> dict:
    digest, size = hashlib.sha256(), 0
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
            size += len(chunk)
    return {"path": str(path.resolve()), "bytes": size, "sha256": digest.hexdigest()}


def record_log_lines(record: dict) -> Iterator[str]:
    """Read every log byte once, preserving splitlines semantics and its hash.

    Full consumption verifies that the parsed bytes are exactly the artifact
    whose digest was captured by load_record. No trust records are omitted.
    """
    path = Path(record["log_path"])
    expected = record["artifacts"]["build.log"]
    digest, size = hashlib.sha256(), 0
    with path.open("rb") as handle:
        for raw in handle:
            digest.update(raw)
            size += len(raw)
            yield from raw.decode("utf-8").splitlines()
    require(size == expected["bytes"] and digest.hexdigest() == expected["sha256"],
            "Log changed while reading: " + str(path))


def write_json_artifact(path: Path, value: object) -> dict:
    """Write the same complete JSON representation without a whole-file copy."""
    require(not path.exists(), "Output artifact already exists: " + str(path))
    temporary = path.with_name(path.name + ".tmp")
    digest, size = hashlib.sha256(), 0
    with temporary.open("xb") as handle:
        for chunk in json.JSONEncoder(indent=2, ensure_ascii=False).iterencode(value):
            data = chunk.encode("utf-8")
            handle.write(data)
            digest.update(data)
            size += len(data)
        handle.write(b"\n")
        digest.update(b"\n")
        size += 1
    require(not path.exists(), "Output artifact appeared during writing: " + str(path))
    temporary.rename(path)
    return {"path": str(path.resolve()), "bytes": size, "sha256": digest.hexdigest()}


def is_source(name: str) -> bool:
    p = PurePosixPath(name)
    return (name == "KltDP.lean" or name.startswith("KltDP/")) and \
        p.suffix == ".lean" and not any(part.startswith("._") for part in p.parts)


def source_hashes(metadata: dict) -> dict[str, str]:
    require(isinstance(metadata.get("files"), dict), "Missing source file manifest")
    result = {}
    for name, info in metadata["files"].items():
        if not is_source(name):
            continue
        require(not PurePosixPath(name).is_absolute() and ".." not in PurePosixPath(name).parts,
                f"Unsafe source manifest path: {name}")
        value = info.get("sha256")
        require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None,
                f"Invalid SHA-256 for {name}")
        result[name] = value
    require("KltDP.lean" in result, "Library entry point absent from source manifest")
    require(TOOLING_SOURCE in result, "Compiled trust implementation absent from source manifest")
    return result


def validate_metadata(metadata: dict, label: str) -> None:
    for key in ("lean_version", "lake_version", "mathlib_head"):
        require(metadata.get(key, {}).get("exit_code") == 0,
                f"{label}: {key} probe did not succeed")
    require(re.search(r"\bversion 4\.19\.0(?:,|\))", metadata["lean_version"]["stdout"]) is not None,
            f"{label}: unexpected Lean version")
    require("Lean version 4.19.0)" in metadata["lake_version"]["stdout"],
            f"{label}: unexpected Lake toolchain")
    require(metadata["mathlib_head"]["stdout"].strip() == DEPENDENCIES["mathlib"],
            f"{label}: unexpected mathlib revision")
    deps = metadata.get("verified_dependencies")
    require(isinstance(deps, list), f"{label}: no verified dependency records")
    require(len(deps) == len(DEPENDENCIES), f"{label}: dependency count mismatch")
    require(len({d["name"] for d in deps}) == len(deps), f"{label}: duplicate dependencies")
    require({d["name"]: d["git_head"] for d in deps} == DEPENDENCIES,
            f"{label}: dependency revisions differ from exact pins")
    require(all(d.get("git_status") == "" for d in deps), f"{label}: dirty dependency checkout")


def resource_caps(role: str, canonical_resource_profile: str = "standard26") -> dict:
    require(role in {"library", "audit"}, "Unknown build-record role")
    require(canonical_resource_profile in CANONICAL_RESOURCE_PROFILES,
            "Unknown canonical resource profile")
    return CAPS if canonical_resource_profile == "standard26" else CAPS256CPU4


def source_path(name: str) -> str:
    """The exact source file of an admitted axiom is its owning module's file."""
    return LITERATURE_MODULES[name].replace(".", "/") + ".lean"


def load_record(path: Path, role: str, *, canonical_resource_profile: str = "standard26",
                allow_audit_rejection: bool = False) -> dict:
    expected_caps = resource_caps(role, canonical_resource_profile)
    require(path.is_dir(), f"{role}: missing build record directory: {path}")
    for name in RECORD_FILES:
        require((path / name).is_file(), f"{role}: missing {name}")
    exit_code = (path / "exit_code.txt").read_text().strip()
    if role == "audit" and allow_audit_rejection:
        # Lean exits with status 1 when #klt_trust_report throws its rejection error.
        require(exit_code in {"0", "1"}, f"{role}: exit was neither zero nor the Lean error status")
    else:
        require(exit_code == "0", f"{role}: exit was not zero")
    before = loads((path / "inputs.json").read_text())
    after = loads((path / "outputs.json").read_text())
    require(isinstance(before, dict) and isinstance(after, dict), f"{role}: malformed metadata")
    validate_metadata(before, f"{role} inputs")
    validate_metadata(after, f"{role} outputs")
    project = (path / "project.txt").read_text().strip()
    require(project == before.get("project") == after.get("project"),
            f"{role}: project directory changed")
    sources = source_hashes(before)
    require(sources == source_hashes(after), f"{role}: Lean sources changed during execution")
    cgroup = loads((path / "cgroup.json").read_text())
    require(cgroup.get("verified") is True and cgroup.get("limits") == expected_caps,
            f"{role}: resource caps were not verified exactly")
    argv = cgroup.get("argv", [])
    require(isinstance(argv, list), f"{role}: command arguments missing")
    require(role in {"library", "audit"}, "Unknown build-record role")
    expected_argv = {"library": ["lake", "build", "KltDP", TOOLING_MODULE],
                     "audit": ["lake", "env", "lean", AUDIT_DRIVER]}[role]
    require(argv == expected_argv, f"{role}: unexpected command or targets: {argv}")
    require(shlex.split((path / "command.sh").read_text()) == expected_argv,
            f"{role}: command.sh differs from cgroup command")
    start = (path / "started_at.txt").read_text().strip()
    end = (path / "completed_at.txt").read_text().strip()
    require(datetime.fromisoformat(start.replace("Z", "+00:00")) <=
            datetime.fromisoformat(end.replace("Z", "+00:00")), f"{role}: invalid timestamps")
    return {"directory": str(path.resolve()), "inputs": before, "outputs": after,
            "sources": sources, "cgroup": cgroup, "started_at": start, "completed_at": end,
            "exit_code": exit_code, "log_path": str((path / "build.log").resolve()),
            "artifacts": {name: artifact(path / name) for name in RECORD_FILES}}


def string_set(value: object, label: str) -> set[str]:
    require(isinstance(value, list) and all(isinstance(n, str) for n in value),
            f"{label}: expected a string array")
    require(len(value) == len(set(value)), f"{label}: duplicate entries")
    return set(value)


def validate_declaration_shape(declaration: dict, native_types: bool = False) -> None:
    for key in ("name", "user_name", "module", "scope", "kind", "type") + (() if native_types else ("type_expression",)):
        require(isinstance(declaration.get(key), str) and bool(declaration[key]),
                f"Declaration missing nonempty string field: {key}")
    name = declaration["name"]
    require(declaration["kind"] in DECLARATION_KINDS, f"{name}: unknown declaration kind")
    for key in ("checked", "unsafe", "partial", "extern", "source_range_present", "noncomputable"):
        require(type(declaration.get(key)) is bool, f"{name}: missing boolean field {key}")
    for key in ("universe_parameters", "direct_dependencies"):
        string_set(declaration.get(key), f"{name}: {key}")
    require("implemented_by" in declaration and
            (declaration["implemented_by"] is None or isinstance(declaration["implemented_by"], str)),
            f"{name}: missing/invalid implementation override field")
    require("reducibility_hints" in declaration, f"{name}: missing reducibility-hint metadata")
    if declaration["kind"] == "definition":
        require(declaration["reducibility_hints"] in {"opaque", "regular", "abbrev"},
                f"{name}: unknown definition reducibility hints")
    else:
        require(declaration["reducibility_hints"] is None,
                f"{name}: nondefinition has definition reducibility hints")
    require("root_policy_passes" in declaration and "closure" in declaration,
            f"{name}: missing policy or closure field")
    require("compiler_cache_owner" in declaration and "compiler_cache_stage" in declaration,
            f"{name}: missing compiler-cache classification fields")
    if declaration["scope"] == "compiler_stage_cache":
        require(isinstance(declaration["compiler_cache_owner"], str) and
                bool(declaration["compiler_cache_owner"]) and
                type(declaration["compiler_cache_stage"]) is int and
                declaration["compiler_cache_stage"] in {1, 2}, f"{name}: invalid cache metadata")
        require(declaration["root_policy_passes"] is None, f"{name}: cache claims logical-root policy")
    else:
        require(declaration["compiler_cache_owner"] is None and declaration["compiler_cache_stage"] is None,
                f"{name}: non-cache declaration has cache metadata")
    if declaration["scope"] == "audit_tooling":
        require(declaration["root_policy_passes"] is None and declaration["closure"] is None,
                f"{name}: malformed tooling exemption")
        return
    if declaration["scope"] == "unsafe_implementation":
        require(declaration["root_policy_passes"] is None,
                f"{name}: unsafe implementation claims logical-root policy")
    elif declaration["scope"] != "compiler_stage_cache":
        require(type(declaration["root_policy_passes"]) is bool, f"{name}: nonboolean root policy")
    closure = declaration["closure"]
    require(isinstance(closure, dict), f"{name}: missing dependency closure")
    require(type(closure.get("passes")) is bool, f"{name}: missing closure pass field")
    count = closure.get("transitive_dependency_count_including_root")
    require(type(count) is int and count > 0, f"{name}: missing dependency count")
    for key in ("transitive_axioms", "forbidden_axioms", "missing_checked_declarations",
                "unsafe_dependencies", "partial_dependencies", "audit_tooling_dependencies",
                "opaque_dependencies", "runtime_override_dependencies"):
        string_set(closure.get(key), f"{name}: {key}")
    if declaration["kind"] == "axiom":
        require(name in closure["transitive_axioms"], f"{name}: axiom root absent from its axiom closure")


def lean_name_identifier(part: str) -> bool:
    """Pinned Lean 4.19 isIdFirst/isIdRest; Python Unicode isalpha differs."""
    def letter_like(c):
        n = ord(c)
        return ((0x3B1 <= n <= 0x3C9 and n != 0x3BB) or
                (0x391 <= n <= 0x3A9 and n not in {0x3A0, 0x3A3}) or
                0x3CA <= n <= 0x3FB or 0x1F00 <= n <= 0x1FFE or
                0x2100 <= n <= 0x214F or 0x1D49C <= n <= 0x1D59F)

    def alpha(c):
        return "a" <= c <= "z" or "A" <= c <= "Z"

    def subscript(c):
        n = ord(c)
        return (0x2080 <= n <= 0x2089 or 0x2090 <= n <= 0x209C or
                0x1D62 <= n <= 0x1D6A or n == 0x2C7C)

    return bool(part) and (alpha(part[0]) or part[0] == "_" or letter_like(part[0])) and all(
        alpha(c) or "0" <= c <= "9" or c in "_'!?" or letter_like(c) or subscript(c)
        for c in part[1:])


def cache_name_parts(rendered: str) -> list[tuple[str, str]]:
    """Conservative canonical interpretation of emitted cache name text.

    Name.toString is not globally injective. This checks textual consistency
    with Lean's already-validated structural cache metadata; it does not
    authenticate Name identity or compiler origin. Unsupported raw/fallback
    spellings fail closed. Never strip quote characters from whole names.
    """
    require(isinstance(rendered, str) and bool(rendered), "Empty cache name")
    parts, cursor = [], 0
    while cursor < len(rendered):
        if rendered[cursor] == "«":
            end = rendered.find("»", cursor + 1)
            require(end >= 0, "Unclosed quoted cache-name component")
            parts.append(("str", rendered[cursor + 1:end]))
            cursor = end + 1
        else:
            end = rendered.find(".", cursor)
            if end < 0:
                end = len(rendered)
            part = rendered[cursor:end]
            if re.fullmatch(r"0|[1-9][0-9]*", part):
                parts.append(("num", part))
            else:
                require(lean_name_identifier(part), "Unsupported bare cache-name component")
                parts.append(("str", part))
            cursor = end
        if cursor < len(rendered):
            require(rendered[cursor] == "." and cursor + 1 < len(rendered),
                    "Malformed cache-name component boundary")
            cursor += 1
    return parts


def render_name_parts(parts: list[tuple[str, str]], escape: bool) -> str:
    """The relevant toStringWithSep case with default isToken=false."""
    rendered = []
    for kind, part in parts:
        if kind == "num" or not escape or lean_name_identifier(part):
            rendered.append(part)
        else:
            require("»" not in part, "Unsupported raw Name.toString fallback")
            rendered.append("«" + part + "»")
    return ".".join(rendered)


def compiler_cache_renderings(name: str, stage: int) -> tuple[str, str]:
    """Return exact emitted owner and stage-one strings from a cache spelling.

    A cache's final string _cstageN disables macro/inaccessible suppression.
    Removing it can re-enable suppression for a hygienic/inaccessible owner.
    Pseudo-root #/? fallback names are outside this conservative subset.
    """
    require(type(stage) is int and stage in {1, 2}, "Invalid compiler-cache stage")
    parts = cache_name_parts(name)
    require(len(parts) >= 2 and parts[-1] == ("str", f"_cstage{stage}"),
            "Cache has a different final component or stage")
    require(not (parts[0][0] == "str" and parts[0][1].startswith(("#", "?"))),
            "Unsupported pseudo-root cache name")
    require(render_name_parts(parts, True) == name, "Noncanonical cache-name spelling")
    owner = parts[:-1]
    index = len(owner) - 1
    while index >= 0 and owner[index][0] == "num":
        index -= 1
    last_string = owner[index][1] if index >= 0 else None
    has_macro_scopes = last_string == "_hyg"
    inaccessible = last_string is not None and ("✝" in last_string or last_string == "_inaccessible")
    escaped_owner = not has_macro_scopes and not inaccessible
    return (render_name_parts(owner, escaped_owner),
            render_name_parts(owner + [("str", "_cstage1")], True))


def validate_compiler_cache(declaration: dict, by_name: dict) -> None:
    """Check the recorded Lean 4.19 compiler conventions, not unforgeable provenance."""
    name = declaration["name"]
    owner_name = declaration["compiler_cache_owner"]
    stage = declaration["compiler_cache_stage"]
    owner = by_name.get(owner_name)
    require(isinstance(owner, dict), f"{name}: missing compiler-cache owner")
    rendered_owner, first_stage_name = compiler_cache_renderings(name, stage)
    require(rendered_owner == owner_name, f"{name}: rendered cache owner differs from metadata")
    require(declaration["kind"] == "definition" and declaration["unsafe"] is True and
            declaration["partial"] is False and declaration["source_range_present"] is False and
            declaration["reducibility_hints"] == "opaque",
            f"{name}: cache definition does not have reviewed compiler shape")
    require(owner["kind"] == "definition" and owner["unsafe"] is False and
            owner["partial"] is False and owner["scope"] == "mathematical_declaration" and
            owner["noncomputable"] is False and
            owner["module"] == declaration["module"], f"{name}: owner is not a same-module safe definition")
    require(declaration["closure"]["passes"] is False and
            name in declaration["closure"]["unsafe_dependencies"],
            f"{name}: cache's unsafe closure was suppressed")
    if stage == 1:
        require(declaration["type_expression"] == owner["type_expression"] and
                declaration["universe_parameters"] == owner["universe_parameters"],
                f"{name}: stage-one type/universe parameters differ from owner")
    else:
        require(declaration["universe_parameters"] == [], f"{name}: stage-two universe parameters are not erased")
        first = by_name.get(first_stage_name)
        require(isinstance(first, dict) and first.get("scope") == "compiler_stage_cache" and
                first.get("compiler_cache_owner") == owner_name and first.get("compiler_cache_stage") == 1,
                f"{name}: stage two lacks validated stage-one pair")
        validate_compiler_cache(first, by_name)


def validate_unsafe_implementation(declaration: dict) -> None:
    """This is an explicit nonlogical boundary, not compiler-origin authentication."""
    name = declaration["name"]
    require(declaration["unsafe"] is True and declaration["source_range_present"] is False,
            f"{name}: unsafe implementation must be unsafe and have no direct source range")
    require(declaration["kind"] in {"axiom", "definition", "opaque"} and declaration["partial"] is False,
            f"{name}: invalid unsafe implementation kind or unpaired partial root")
    require(declaration["root_policy_passes"] is None,
            f"{name}: unsafe implementation cannot claim logical-root policy")
    require(declaration["closure"]["passes"] is False and
            name in declaration["closure"]["unsafe_dependencies"],
            f"{name}: unsafe implementation's full unsafe closure was suppressed")


def parse_inventory(log: str | Iterable[str], admission: dict, itemize: dict | None = None) -> dict:
    """Validate the complete trust report.

    `itemize` is None for the strict certificate. In the scoped itemize mode it is
    {"roots": [logical root names], "exit_code": audit exit status}; KLT_TRUST_FAILURE
    records are then admitted only under the exact conditions of validate_itemized_failures.
    """
    require(isinstance(admission.get("entries"), list) and
            all(isinstance(entry, dict) for entry in admission["entries"]) and
            [entry.get("name") for entry in admission["entries"]] == LITERATURE_NAMES,
            "Inventory requires the validated twenty-eight-entry literature registry")
    records = []
    rejection_lines, other_error_lines = [], []
    lines = log.splitlines() if isinstance(log, str) else log
    for line_number, line in enumerate(lines, 1):
        # The auditor's own rejection message quotes the KLT_TRUST_FAILURE tag; classify it first.
        rejection = REJECTION_MESSAGE.match(line)
        if rejection is not None:
            require(itemize is not None, f"Audit log contains the trust rejection message on line {line_number}")
            rejection_lines.append(int(rejection.group(1)))
            continue
        match = re.search(r"\b(KLT_TRUST_[A-Z_]+)\b", line)
        if match is None:
            if itemize is not None and re.search(r"(^|: )error:", line) is not None:
                other_error_lines.append(line_number)
            continue
        tag = match.group(1)
        require(tag in TAGS, f"Unknown trust tag on line {line_number}: {tag}")
        payload = loads(line[match.end():].strip())
        require(isinstance(payload, dict), f"Non-object trust payload on line {line_number}")
        records.append({"tag": tag, "log_line": line_number, "payload": payload})
    require(records, "No compiled trust records in audit log")
    grouped = {tag: [r for r in records if r["tag"] == tag] for tag in TAGS}
    failures = [r["payload"] for r in grouped["KLT_TRUST_FAILURE"]]
    if itemize is None:
        require(not failures, "Audit emitted KLT_TRUST_FAILURE")
    else:
        require(not other_error_lines, "Audit log has Lean errors other than the trust rejection: lines " +
                ", ".join(str(n) for n in other_error_lines[:5]))
        if failures:
            require(itemize.get("exit_code") == "1" and rejection_lines == [len(failures)],
                    "Failed audit must exit with Lean status 1 and print exactly one rejection message naming the failure count")
        else:
            require(itemize.get("exit_code") == "0" and not rejection_lines,
                    "Audit without failures must exit zero without a rejection message")
    for tag in ("KLT_TRUST_INVENTORY_BEGIN", "KLT_TRUST_INVENTORY_END", "KLT_TRUST_AUDIT"):
        require(len(grouped[tag]) == 1, f"Expected exactly one {tag}")
    declarations = [r["payload"] for r in grouped["KLT_TRUST_DECL"]]
    require([r["tag"] for r in records] == ["KLT_TRUST_INVENTORY_BEGIN"] +
            ["KLT_TRUST_DECL"] * len(declarations) +
            ["KLT_TRUST_INVENTORY_END"] + ["KLT_TRUST_FAILURE"] * len(failures) + ["KLT_TRUST_AUDIT"],
            "Trust markers out of order, duplicated, or truncated")
    begin = grouped["KLT_TRUST_INVENTORY_BEGIN"][0]["payload"]
    end = grouped["KLT_TRUST_INVENTORY_END"][0]["payload"]
    summary = grouped["KLT_TRUST_AUDIT"][0]["payload"]
    require(begin.get("schema") == summary.get("schema") and
            begin.get("schema") in {SCHEMA, NATIVE_TYPE_SCHEMA}, "Unsupported trust schema")
    native_types = begin["schema"] == NATIVE_TYPE_SCHEMA
    require(begin.get("compiler_cache_policy") == summary.get("compiler_cache_policy") == CACHE_POLICY,
            "Unexpected or missing compiler-cache policy profile")
    for record in (begin, end):
        require(type(record.get("declaration_count")) is int, "Missing integer declaration count")
    for key in ("mathematical_declaration_count", "runtime_companion_count",
                "compiler_stage_cache_count", "unsafe_implementation_count", "failed_declaration_count"):
        require(type(summary.get(key)) is int and summary[key] >= 0, f"Missing integer summary field: {key}")
    require(begin.get("declaration_count") == end.get("declaration_count") == len(declarations),
            "Declaration counts do not match complete inventory")
    names = [d.get("name") for d in declarations]
    require(all(isinstance(n, str) and n for n in names) and len(set(names)) == len(names),
            "Declaration names missing or duplicated")
    require(string_set(begin.get("foundational_axioms"), "Foundations") == FOUNDATIONS,
            "Foundational allowlist differs from expected policy")
    require(begin.get("literature_axioms") == summary.get("literature_axioms") == LITERATURE_NAMES,
            "Literature lists differ from the twenty-eight registered admissions")
    by_name = dict(zip(names, declarations))
    legacy_type_names = set(LITERATURE_NAMES)
    if native_types:
        for declaration in declarations:
            if declaration.get("scope") == "compiler_stage_cache" and declaration.get("compiler_cache_stage") == 1:
                legacy_type_names.update((declaration.get("name"), declaration.get("compiler_cache_owner")))
    for declaration in declarations:
        validate_declaration_shape(declaration, native_types)
        if native_types:
            if declaration["name"] in legacy_type_names:
                require(isinstance(declaration.get("type_expression"), str) and bool(declaration["type_expression"]),
                        f"{declaration['name']}: literal legacy type expression is required")
            else:
                validate_native_type_reference(declaration)
    for approved in admission["entries"]:
        verify_declared_axiom(approved, declarations)
    failed_names = [failure.get("name") for failure in failures]
    require(all(isinstance(n, str) and n in by_name for n in failed_names) and
            len(set(failed_names)) == len(failed_names), "Failure records name unknown or duplicated declarations")
    failed = set(failed_names)
    mathematical, companions, tooling, caches, unsafe_implementations = [], [], [], [], []
    all_axioms = set()
    for declaration in declarations:
        name = declaration["name"]
        scope = declaration.get("scope")
        require(declaration.get("checked") is True, f"Unchecked declaration: {name}")
        if scope == "audit_tooling":
            require(declaration.get("module") == TOOLING_MODULE,
                    f"Unexpected audit-tooling exemption: {name}")
            tooling.append(declaration)
            continue
        if scope == "compiler_stage_cache":
            validate_compiler_cache(declaration, by_name)
            caches.append(declaration)
            continue
        if scope == "unsafe_implementation":
            validate_unsafe_implementation(declaration)
            unsafe_implementations.append(declaration)
            continue
        require(scope in {"mathematical_declaration", "safe_definition_runtime_companion"},
                f"Unknown declaration scope: {name}")
        if name in failed:
            require(scope == "mathematical_declaration" and declaration.get("root_policy_passes") is False,
                    f"Failure record does not match a rejected logical root: {name}")
            closure = declaration.get("closure")
            require(isinstance(closure, dict), f"Missing dependency closure: {name}")
            all_axioms.update(string_set(closure.get("transitive_axioms"), f"{name} axioms"))
            mathematical.append(declaration)
            continue
        require(declaration.get("root_policy_passes") is True, f"Root policy rejected {name}")
        require(declaration.get("unsafe") is False, f"Unsafe root: {name}")
        closure = declaration.get("closure")
        require(isinstance(closure, dict), f"Missing dependency closure: {name}")
        axioms = string_set(closure.get("transitive_axioms"), f"{name} axioms")
        require(axioms <= FOUNDATIONS | set(LITERATURE_NAMES), f"Forbidden transitive axiom: {name}")
        all_axioms.update(axioms)
        require(not any(by_name.get(dependency, {}).get("scope") in
                        {"compiler_stage_cache", "unsafe_implementation"}
                        for dependency in declaration["direct_dependencies"]),
                f"Logical root directly depends on an unsafe implementation: {name}")
        for key in ("forbidden_axioms", "missing_checked_declarations", "unsafe_dependencies",
                    "audit_tooling_dependencies"):
            require(closure.get(key) == [], f"{name}: nonempty {key}")
        if scope == "mathematical_declaration":
            require(declaration.get("partial") is False and closure.get("passes") is True and
                    closure.get("partial_dependencies") == [], f"Partial/failed logical root: {name}")
            mathematical.append(declaration)
        else:
            require(declaration["partial"] is True, f"Runtime companion is not partial: {name}")
            for dependency in closure["partial_dependencies"]:
                if dependency in by_name:
                    require(by_name[dependency].get("scope") == "safe_definition_runtime_companion",
                            f"Unclassified project partial dependency: {name}: {dependency}")
            companions.append(declaration)
    require(mathematical, "No mathematical declarations audited")
    require(summary.get("mathematical_declaration_count") == len(mathematical) and
            summary.get("runtime_companion_count") == len(companions) and
            summary.get("compiler_stage_cache_count") == len(caches) and
            summary.get("unsafe_implementation_count") == len(unsafe_implementations),
            "Summary logical/nonlogical declaration count mismatch")
    if failures:
        require(summary.get("status") == "dependency_policy_failed" and
                summary.get("failed_declaration_count") == len(failures), "Failure summary differs from failure records")
    else:
        require(summary.get("status") == "dependency_policy_passed" and
                summary.get("failed_declaration_count") == 0, "No successful dependency-policy summary")
    require(string_set(summary.get("transitive_axioms"), "Summary axioms") == all_axioms,
            "Summary axiom set differs from declaration closures")
    require(summary.get("manuscript_completeness") == "not_assessed_by_dependency_audit",
            "Unexpected semantic-completion claim in audit record")
    itemized = None
    if itemize is not None:
        itemized = validate_itemized_failures(itemize["roots"], failures, by_name)
    return {"records": records, "begin": begin, "summary": summary, "declarations": declarations,
            "mathematical": mathematical, "companions": companions, "tooling": tooling,
            "compiler_stage_caches": caches, "unsafe_implementations": unsafe_implementations,
            "itemized_nonroot_failures": itemized}


def reachable_project_declarations(root: str, by_name: dict) -> set[str]:
    """Project declarations reachable from a root along the exported direct-dependency edges.

    Every dependency path from a project declaration to another project declaration
    passes through project declarations only: the pinned Mathlib/core constants were
    compiled before the project and cannot refer to it. The inventory exports the same
    direct edges the auditor traverses, so this is an independent replay of the auditor's
    reachability restricted to the project.
    """
    seen, pending = set(), [root]
    while pending:
        name = pending.pop()
        if name in seen or name not in by_name:
            continue
        seen.add(name)
        pending.extend(by_name[name].get("direct_dependencies", []))
    return seen


def validate_itemized_failures(roots: list[str], failures: list[dict], by_name: dict) -> dict:
    """The scoped criterion of --itemize-nonroot-failures; every clause is necessary.

    Each failed declaration must be the `_unsafe_rec` companion Lean generates for a
    source-level `partial def`: a partial, safe-flagged definition whose owner (the name
    without the suffix) is the checked opaque wrapper in the same module and itself passes
    the policy, and whose closure fails only through partial dependencies that are
    themselves such companions (no forbidden axiom, missing, unsafe or tooling
    dependency). Each listed root must pass the policy with an empty partial-dependency
    list, and no failed declaration may be reachable from it along the exported edges.
    This lists failures; it does not approve the metaprogramming code that produced them.
    """
    require(isinstance(roots, list) and roots and all(isinstance(r, str) and r for r in roots) and
            len(set(roots)) == len(roots), "Itemize mode requires a nonempty list of distinct logical roots")
    failed = {failure["name"] for failure in failures}
    rows = []
    for failure in failures:
        name = failure["name"]
        row = by_name[name]
        require(set(failure) == {"name", "closure"} and failure["closure"] == row.get("closure"),
                f"Failure record differs from the declaration's own closure: {name}")
        require(name.endswith(UNSAFE_REC_SUFFIX) and len(name) > len(UNSAFE_REC_SUFFIX),
                f"Failed declaration is not a partial-definition companion: {name}")
        owner_name = name[:-len(UNSAFE_REC_SUFFIX)]
        owner = by_name.get(owner_name)
        require(isinstance(owner, dict) and owner.get("kind") == "opaque" and
                owner.get("module") == row.get("module") and
                owner.get("scope") == "mathematical_declaration" and owner.get("root_policy_passes") is True,
                f"Companion owner is not a passing opaque wrapper in the same module: {name}")
        require(row.get("kind") == "definition" and row.get("partial") is True and row.get("unsafe") is False,
                f"Failed companion is not a partial safe-flagged definition: {name}")
        closure = row["closure"]
        require(closure.get("passes") is False, f"Failed companion reports a passing closure: {name}")
        for key in ("forbidden_axioms", "missing_checked_declarations", "unsafe_dependencies",
                    "audit_tooling_dependencies"):
            require(closure.get(key) == [], f"Failed companion has a non-partial failure cause: {name}: {key}")
        partials = string_set(closure.get("partial_dependencies"), f"{name}: partial_dependencies")
        require(partials and partials <= failed,
                f"Failed companion depends on a partial declaration that is not itself an itemized companion: {name}")
        require(string_set(closure.get("transitive_axioms"), f"{name} axioms") <= FOUNDATIONS | set(LITERATURE_NAMES),
                f"Failed companion has a forbidden transitive axiom: {name}")
        rows.append({"name": name, "module": row["module"], "kind": row["kind"], "owner": owner_name,
                     "owner_kind": owner["kind"], "partial_dependencies": sorted(partials),
                     "transitive_axioms": closure["transitive_axioms"],
                     "transitive_dependency_count_including_root": closure["transitive_dependency_count_including_root"]})
    root_rows = []
    for root in roots:
        row = by_name.get(root)
        require(isinstance(row, dict), f"Listed logical root is absent from the inventory: {root}")
        closure = row.get("closure") or {}
        require(row.get("scope") == "mathematical_declaration" and row.get("root_policy_passes") is True and
                closure.get("passes") is True and closure.get("partial_dependencies") == [] and
                closure.get("unsafe_dependencies") == [] and closure.get("missing_checked_declarations") == [] and
                closure.get("forbidden_axioms") == [] and closure.get("audit_tooling_dependencies") == [],
                f"Listed logical root does not pass the policy with a clean closure: {root}")
        reachable = reachable_project_declarations(root, by_name)
        hits = sorted(failed & reachable)
        require(not hits, f"Listed logical root reaches an itemized failure along exported edges: {root}: {hits}")
        modules = {by_name[n]["module"] for n in reachable}
        root_rows.append({"name": root, "module": row["module"], "kind": row["kind"],
                          "transitive_axioms": closure["transitive_axioms"],
                          "transitive_dependency_count_including_root": closure["transitive_dependency_count_including_root"],
                          "reachable_project_declarations": len(reachable),
                          "reachable_project_modules": len(modules),
                          "reachable_declarations_in_failure_modules": sorted(
                              n for n in reachable if by_name[n]["module"] in {r["module"] for r in rows})})
    return {"criterion": "Every failed declaration is a source-level partial-definition companion (`_unsafe_rec`) whose only failure cause is partial safety, and no listed logical root reaches any of them",
            "failures": rows, "failure_count": len(rows),
            "failure_modules": sorted({r["module"] for r in rows}), "roots": root_rows}


def native_type_name(parts: object) -> str:
    """Render exact components using Lean 4.19 default Name.toString rules.

    Components remain in the record for lossless native lookup; rendering is
    only a consistency check and is not claimed to be injective.
    """
    require(isinstance(parts, list) and bool(parts), "Native declaration Name must be nonanonymous")
    for part in parts:
        require(isinstance(part, list) and len(part) == 2 and
                part[0] in {"str", "num"} and isinstance(part[1], str),
                "Malformed native declaration Name component")
        if part[0] == "num":
            require(re.fullmatch(r"0|[1-9][0-9]*", part[1]) is not None,
                    "Noncanonical native Name numeric component")
    last_string = next((value for kind, value in reversed(parts) if kind == "str"), None)
    raw = (last_string is not None and
           (last_string == "_hyg" or "✝" in last_string or last_string == "_inaccessible")) or \
          parts == [["str", "_"]] or (parts[0][0] == "str" and parts[0][1].startswith(("#", "?")))
    return ".".join(value if kind == "num" or raw or lean_name_identifier(value) or "»" in value
                    else "«" + value + "»" for kind, value in parts)


def validate_native_type_reference(declaration: dict) -> None:
    ref = declaration.get("type_expression")
    require(isinstance(ref, dict) and set(ref) ==
            {"encoding", "module", "declaration", "name_parts", "artifact"},
            f"{declaration['name']}: malformed native type reference")
    require(ref["encoding"] == NATIVE_TYPE_ENCODING and
            ref["module"] == declaration["module"] and ref["declaration"] == declaration["name"] and
            native_type_name(ref["name_parts"]) == declaration["name"],
            f"{declaration['name']}: native type reference owner/name differs")
    expected = ".lake/build/lib/lean/" + declaration["module"].replace(".", "/") + ".olean"
    require(ref["artifact"] == expected, f"{declaration['name']}: noncanonical native artifact")


def validate_native_type_objects(library: dict, audit: dict, project: Path, inventory: dict,
                                 before_path: Path | None, after_path: Path | None,
                                 profile: str) -> dict | None:
    """Bind existing source/object continuity sidecars; never execute Lean.

    The reviewed emitter selects the actual imported checked ConstantInfo.
    These retained objects plus exact Name components permit native type
    reconstruction; the parser does not import the objects or certify proofs.
    """
    native = inventory["begin"]["schema"] == NATIVE_TYPE_SCHEMA
    if not native:
        require(before_path is None and after_path is None,
                "Native object sidecars supplied for a legacy inventory")
        return None
    require(before_path is not None and after_path is not None,
            "Native types require both original source/object continuity sidecars")
    require(library["sources"] == audit["sources"], "Native source snapshots differ")
    sources = library["sources"]
    observations, descriptors = [], []
    for path, phase in ((before_path, "before_canonical_audit"), (after_path, "after_canonical_audit")):
        require(path.is_file() and not path.is_symlink(), "Missing/symlinked native object manifest")
        data = path.read_bytes()
        observed = loads(data.decode("utf-8"))
        require(isinstance(observed, dict) and
                observed.get("schema") == "klt-canonical429-source-object-observation-v1" and
                observed.get("status") == "observed_source_object_pairs_not_acceptance" and
                observed.get("phase") == phase and observed.get("profile") == profile and
                observed.get("intended_job") == "canonical_audit" and
                observed.get("preceding_build") == Path(library["directory"]).name and
                observed.get("linked_build_id") == (None if phase == "before_canonical_audit" else
                                                    Path(audit["directory"]).name),
                "Native object observation has wrong schema/phase/profile/job binding")
        require(isinstance(observed.get("configuration_sha256"), str) and
                re.fullmatch(r"[0-9a-f]{64}", observed["configuration_sha256"]) is not None,
                "Native object observation lacks configuration binding")
        rows = observed.get("verified")
        require(isinstance(rows, dict) and set(rows) == set(sources),
                "Native object observation does not cover the exact audited source set")
        for source, row in rows.items():
            require(isinstance(row, dict) and set(row) ==
                    {"source_sha256", "olean_path", "olean_bytes", "olean_sha256"} and
                    row["source_sha256"] == sources[source] and
                    row["olean_path"] == ".lake/build/lib/lean/" + source[:-5] + ".olean" and
                    type(row["olean_bytes"]) is int and row["olean_bytes"] > 0 and
                    isinstance(row["olean_sha256"], str) and
                    re.fullmatch(r"[0-9a-f]{64}", row["olean_sha256"]) is not None,
                    "Native object/source descriptor mismatch: " + source)
        descriptors.append({"path": str(path.resolve()), "bytes": len(data), "sha256": sha256(data)})
        observations.append(observed)
    before, after = observations
    require(before["configuration_sha256"] == after["configuration_sha256"] and
            before["verified"] == after["verified"], "Native objects/configuration changed during audit")
    def stamp(value: str) -> datetime:
        require(isinstance(value, str), "Missing native observation timestamp")
        result = datetime.fromisoformat(value.replace("Z", "+00:00"))
        require(result.tzinfo is not None, "Native timestamp has no timezone")
        return result
    # Native runner timestamps have one-second precision; observation timestamps
    # retain microseconds. The captured start denotes its half-open one-second interval.
    require(stamp(library["completed_at"]) <= stamp(before.get("at_utc")) and
            stamp(before.get("at_utc")) <= stamp(after.get("at_utc")) and
            stamp(before.get("at_utc")) < stamp(audit["started_at"]) + timedelta(seconds=1) and
            stamp(audit["started_at"]) <= stamp(audit["completed_at"]) <= stamp(after.get("at_utc")),
            "Native source/object observations do not bracket the actual audit")
    modules = {source[:-5].replace("/", "."): source for source in sources}
    refs = [row for row in inventory["declarations"] if isinstance(row["type_expression"], dict)]
    for declaration in refs:
        ref = declaration["type_expression"]
        require(ref["module"] in modules and
                ref["artifact"] == before["verified"][modules[ref["module"]]]["olean_path"],
                "Native reference owner absent from bound source/object manifest: " + declaration["name"])
    for source, row in before["verified"].items():
        path = project / row["olean_path"]
        require(path.is_file() and not path.is_symlink() and path.resolve() == path,
                "Native object missing or redirected: " + source)
        require(artifact(path) == {"path": str(path), "bytes": row["olean_bytes"], "sha256": row["olean_sha256"]},
                "Retained native object differs from audited pair: " + source)
    for descriptor in descriptors:
        require(artifact(Path(descriptor["path"])) == descriptor, "Native object manifest changed while reading")
    return {"encoding": NATIVE_TYPE_ENCODING, "before_manifest": descriptors[0],
            "after_manifest": descriptors[1], "configuration_sha256": before["configuration_sha256"],
            "source_count": len(sources), "reference_count": len(refs),
            "referenced_object_count": len({row["type_expression"]["artifact"] for row in refs}),
            "verified": before["verified"],
            "scope": "Exact retained checked-module objects and source/Name references; no Lean execution or proof checking by this parser"}


def validate_driver_format(data: bytes, format_record: dict | None = None) -> dict:
    """Recognize exact reviewed programs, never strip comments or accept extra commands.

    A legacy program additionally needs an explicit record binding its declared
    format to these exact bytes. Such a record identifies the input; it is not
    compilation evidence or an authorization to accept other Lean commands.
    """
    if data == REPORT_DRIVER:
        driver_format = REPORT_DRIVER_FORMAT
    elif data == STREAM_REPORT_DRIVER:
        driver_format = STREAM_REPORT_DRIVER_FORMAT
    elif data == NATIVE_REPORT_DRIVER:
        driver_format = NATIVE_REPORT_DRIVER_FORMAT
    elif data in (LEGACY_DRIVER, LEGACY_GENERATED_DRIVER):
        driver_format = LEGACY_DRIVER_FORMAT
        require(format_record is not None,
                "Historical audit driver requires an explicit --driver-format-record")
    else:
        raise ValidationError("Unexpected audit driver program; only exact reviewed driver bytes are accepted")
    fingerprint = {"schema": DRIVER_FORMAT_SCHEMA, "format": driver_format,
                   "path": AUDIT_DRIVER, "bytes": len(data), "sha256": sha256(data)}
    if format_record is not None:
        require(isinstance(format_record, dict) and set(format_record) == set(fingerprint),
                "Malformed audit driver format record")
        require(type(format_record["bytes"]) is int and format_record == fingerprint,
                "Audit driver format record does not match the exact driver format and bytes")
    return fingerprint


def validate_driver(audit: dict, project: Path, format_record_path: Path | None = None) -> dict:
    driver = project / AUDIT_DRIVER
    require(driver.is_file(), "Audit driver is missing")
    data = driver.read_bytes()
    driver_hashes = [audit[phase]["files"].get(AUDIT_DRIVER, {}).get("sha256")
                     for phase in ("inputs", "outputs")]
    require(len(set(driver_hashes)) == 1 and driver_hashes[0] == sha256(data),
            "Audit driver changed or lacks recorded hashes")
    record = None
    if format_record_path is not None:
        record = loads(format_record_path.read_text())
        require(isinstance(record, dict), "Explicit audit driver format record must be a JSON object")
    fingerprint = validate_driver_format(data, record)
    if fingerprint["format"] in {STREAM_REPORT_DRIVER_FORMAT, NATIVE_REPORT_DRIVER_FORMAT}:
        tooling_sha = NATIVE_TOOLING_SHA256 if fingerprint["format"] == NATIVE_REPORT_DRIVER_FORMAT else STREAM_TOOLING_SHA256
        require(all(audit[phase]["files"].get(TOOLING_SOURCE, {}).get("sha256") ==
                    tooling_sha for phase in ("inputs", "outputs")) and
                sha256((project / TOOLING_SOURCE).read_bytes()) == tooling_sha,
                "Streaming driver requires the exact reviewed opt-in trust emitter")
    return {"artifact": artifact(driver), "format": fingerprint,
            "explicit_format_record": None if format_record_path is None else {
                "artifact": artifact(format_record_path), "record": record}}


def bind_admission_artifact(library: dict, audit: dict, project: Path,
                            name: str, expected_hash: str | None = None) -> tuple[bytes, dict]:
    """Capture bytes and bind their exact size/hash across all four snapshots."""
    require(isinstance(name, str) and bool(name) and
            not PurePosixPath(name).is_absolute() and "\\" not in name and
            not any(part in {"", ".", ".."} for part in name.split("/")),
            "Unsafe admission artifact path")
    path = project / name
    require(path.is_file(), f"Missing admission artifact: {name}")
    data = path.read_bytes()
    info = {"path": str(path.resolve()), "bytes": len(data), "sha256": sha256(data)}
    if expected_hash is not None:
        require(info["sha256"] == expected_hash, f"Admission artifact differs from review: {name}")
    for record in (library, audit):
        for phase in ("inputs", "outputs"):
            archived = record[phase]["files"].get(name)
            require(isinstance(archived, dict) and type(archived.get("bytes")) is int and
                    archived["bytes"] == info["bytes"] and archived.get("sha256") == info["sha256"],
                    f"Admission artifact differs across snapshots/current source: {name}")
    return data, info


def verify_declared_axiom(entry: dict, declarations: list[dict]) -> dict:
    """The registered axiom must occur exactly once with the registered module, safety and types."""
    name = entry["name"]
    matches = [row for row in declarations if row.get("name") == name]
    require(len(matches) == 1, f"Admitted axiom must occur exactly once in the full inventory: {name}")
    row = matches[0]
    require(row.get("user_name") == name and row.get("module") == entry["module"] and
            row.get("kind") == "axiom" and row.get("checked") is True and
            row.get("unsafe") is False and row.get("partial") is False and
            row.get("scope") == "mathematical_declaration" and
            row.get("source_range_present") is True and
            row.get("universe_parameters") == entry["universe_parameters"],
            f"Admitted axiom has wrong module, kind, safety, scope or universe telescope: {name}")
    for field, binding in (("type_expression", "type_expression_sha256"), ("type", "printed_type_sha256")):
        require(isinstance(row.get(field), str) and
                sha256(row[field].encode("utf-8")) == entry[binding],
                f"Admitted axiom {field} differs from the registered type hash: {name}")
    return row


def validate_literature_admission(library: dict, audit: dict, project: Path) -> dict:
    """Bind the single v7 registry: exact names, modules, source and type hashes for all 28.

    The registry bytes must be identical in both build snapshots and locally. Each entry's
    source hash must equal the archived and current source; the type hashes are checked
    against the emitted inventory rows by verify_declared_axiom. The four historical
    registries are pinned pointers and are rehashed when present. Nothing here assesses
    the mathematical meaning of an admission or manuscript completion.
    """
    registry_bytes, registry_artifact = bind_admission_artifact(library, audit, project, LITERATURE_REGISTRY)
    registry = loads(registry_bytes.decode("utf-8"))
    require(isinstance(registry, dict) and registry.get("schema") == LITERATURE_REGISTRY_SCHEMA and
            registry.get("policy") == CACHE_POLICY, "Literature registry schema or policy differs")
    require(string_set(registry.get("ordinary_axioms"), "Registry foundations") == FOUNDATIONS,
            "Registry foundational axioms differ from the fixed policy")
    entries = registry.get("active_literature_axioms")
    require(isinstance(entries, list) and all(isinstance(entry, dict) for entry in entries) and
            [entry.get("name") for entry in entries] == LITERATURE_NAMES,
            "Registry entries differ from the twenty-eight admissions in canonical order")
    history = []
    for entry in entries:
        name = entry["name"]
        require(REGISTRY_ENTRY_KEYS <= set(entry) <= REGISTRY_ENTRY_KEYS | {"original_registry"},
                f"Registry entry has missing or unknown fields: {name}")
        source = source_path(name)
        require(entry["module"] == LITERATURE_MODULES[name] and entry["source_path"] == source,
                f"Registry module or source path differs from the admission table: {name}")
        for field in ("source_sha256", "type_expression_sha256", "printed_type_sha256"):
            require(isinstance(entry[field], str) and re.fullmatch(r"[0-9a-f]{64}", entry[field]) is not None,
                    f"Registry entry has an invalid {field}: {name}")
        string_set(entry["universe_parameters"], f"{name}: universe_parameters")
        require(library["sources"].get(source) == audit["sources"].get(source) == entry["source_sha256"],
                f"Admitted axiom source is absent from or differs in the compiled snapshot: {name}")
        require(sha256((project / source).read_bytes()) == entry["source_sha256"],
                f"Admitted axiom source differs locally: {name}")
        published = entry["published_source"]
        require(isinstance(published, dict) and bool(published) and
                all(isinstance(key, str) and bool(key) for key in published),
                f"Registry entry lacks a published source: {name}")
        if name in HISTORICAL_REGISTRIES:
            path, digest = HISTORICAL_REGISTRIES[name]
            require(entry.get("original_registry") == {"path": path, "sha256": digest},
                    f"Historical registry pointer differs from its pinned hash: {name}")
            present = (project / path).is_file()
            if present:
                require(sha256((project / path).read_bytes()) == digest,
                        f"Historical registry file differs from its pinned hash: {path}")
            history.append({"name": name, "path": path, "sha256": digest, "present_locally": present})
        else:
            require("original_registry" not in entry, f"Unexpected historical registry pointer: {name}")
    contract = {"registry_path": LITERATURE_REGISTRY, "registry_sha256": registry_artifact["sha256"],
                "files": [{"path": source_path(name), "name": name, "sha256": library["sources"][source_path(name)]}
                          for name in LITERATURE_NAMES]}
    return {"entries": entries, "source_report_contract": contract,
            "public_evidence": {"policy": CACHE_POLICY, "registry": registry_artifact, "entries": entries,
                                "historical_registries": history, "source_report_contract": contract,
                                "scope": "Twenty-eight exact literature admissions bound by name, module, source hash and type hashes; no use-site semantics or manuscript completion authorized"}}


def validate_source_lint(library: dict, audit: dict, project: Path, admission: dict,
                         itemize: bool = False) -> dict:
    """Bind and reproduce the reviewed Python source gate; never execute Lean.

    Reproduction is restricted to the archived Lean snapshot. Additional local
    project modules remain unaudited and are reported by validate_sources.
    No Python module is loaded until its bytes match the reviewed digest.
    In itemize mode the report may carry rejections whose tokens are exactly `elab`
    or `partial` (custom elaborator code) and review findings; all are reproduced from
    the bound bytes and listed in the returned record. Any other rejection, and any
    import-gate rejection, still refuses.
    """
    require(isinstance(SOURCE_LINTER_SHA256, str) and
            re.fullmatch(r"[0-9a-f]{64}", SOURCE_LINTER_SHA256) is not None,
            "Source-gate implementation has not yet received its reviewed hash")
    artifacts, artifact_bytes = {}, {}
    for name in (SOURCE_LINTER, SOURCE_LINT_REPORT):
        path = project / name
        require(path.is_file(), f"Missing source-gate artifact: {name}")
        data = path.read_bytes()
        info = {"path": str(path.resolve()), "bytes": len(data), "sha256": sha256(data)}
        for record in (library, audit):
            for phase in ("inputs", "outputs"):
                archived = record[phase]["files"].get(name)
                require(isinstance(archived, dict) and
                        type(archived.get("bytes")) is int and
                        archived["bytes"] == info["bytes"] and archived.get("sha256") == info["sha256"],
                        f"Source-gate artifact differs across snapshots/current source: {name}")
        artifacts[name] = info
        artifact_bytes[name] = data
    require(artifacts[SOURCE_LINTER]["sha256"] == SOURCE_LINTER_SHA256,
            "Source-gate implementation differs from the reviewed linter")
    report = loads(artifact_bytes[SOURCE_LINT_REPORT].decode("utf-8"))
    require(isinstance(report, dict), "Source-lint report must be a JSON object")
    require(report.get("schema") == "klt-source-lint-v1" and
            report.get("source_policy_profile") == CACHE_POLICY and
            report.get("status") in ({"source_lint_passed", "source_lint_rejected", "source_policy_review_required"}
                                     if itemize else {"source_lint_passed"}) and
            report.get("linter_sha256") == SOURCE_LINTER_SHA256,
            "Source-lint schema/profile/status/linter binding is invalid")
    require(report.get("proof_status") == "not_assessed_by_source_lint" and
            report.get("literature_axiom_allowlist") == LITERATURE_NAMES,
            "Source lint claims proof completion or an unauthorized literature allowlist")
    require(report.get("import_policy_rejections") == [], "Source-lint admission has missing or nonempty import_policy_rejections")
    for key in ("mathematical_source_rejections", "mathematical_source_reviews"):
        recorded = report.get(key)
        require(isinstance(recorded, list) and all(isinstance(row, dict) for row in recorded),
                f"Source-lint report has a malformed {key}")
        if not itemize:
            require(recorded == [], f"Source-lint admission has nonempty {key}")
    require(all(row.get("severity") == "reject" and row.get("token") in ITEMIZED_SOURCE_TOKENS
                for row in report["mathematical_source_rejections"]),
            "Source-lint rejections other than elab/partial elaborator code cannot be itemized")
    rows = report.get("files")
    require(isinstance(rows, list) and all(isinstance(row, dict) for row in rows),
            "Source-lint source inventory is missing or malformed")
    paths = [row.get("path") for row in rows]
    require(all(isinstance(name, str) and is_source(name) for name in paths) and
            len(paths) == len(set(paths)) and set(paths) == set(library["sources"]),
            "Source-lint file inventory differs from the complete archived Lean snapshot")
    source_texts = {}
    for row in rows:
        name = row["path"]
        require(set(row) == {"path", "sha256", "scope", "findings"},
                f"Malformed source-lint row: {name}")
        data = (project / name).read_bytes()
        require(row["sha256"] == library["sources"][name] and sha256(data) == row["sha256"],
                f"Source-lint source hash differs from archived/current source: {name}")
        source_texts[name] = data.decode("utf-8")
        expected_scope = "audit_tooling" if name == TOOLING_SOURCE else "mathematical_source"
        require(row["scope"] == expected_scope and isinstance(row["findings"], list),
                f"Invalid source-lint scope or findings: {name}")

    linter = reviewed_linter(project, artifact_bytes[SOURCE_LINTER])
    expected_lexical = {
        "rejected_leaf_names": sorted(linter.REJECT),
        "rejected_leaf_prefixes": sorted(linter.REJECT_PREFIXES),
        "tooling_exemption": TOOLING_SOURCE,
        "reviewed_attribute_commands": list(linter.REVIEWED_ATTRIBUTE_COMMANDS),
        "reviewed_attribute_followers": sorted(linter.REVIEWED_ATTRIBUTE_FOLLOWERS),
        "reviewed_declaration_attributes": sorted(linter.REVIEWED_DECLARATION_ATTRIBUTES),
        "review_findings_block_admission": True,
    }
    require(report.get("lexical_policy") == expected_lexical,
            "Reported lexical policy differs from the reviewed source gate")
    require(report.get("literature_admission") == admission["source_report_contract"],
            "Source-report literature admission differs from validated registry/helper/type")
    require(list(linter.LITERATURE_AXIOM_FILES) == [(source_path(name), name) for name in LITERATURE_NAMES] and
            linter.LITERATURE_REGISTRY == LITERATURE_REGISTRY and
            linter.LITERATURE_REGISTRY_SCHEMA == LITERATURE_REGISTRY_SCHEMA,
            "Source-gate literature allowlist differs from the parser's twenty-eight admissions")
    imports, admitted_findings = [], []
    reproduced_rejections, reproduced_reviews = [], []
    for row in rows:
        name = row["path"]
        source = source_texts[name]
        require(row["findings"] == linter.findings(source),
                f"Recorded source findings fail reproduction: {name}")
        if name != TOOLING_SOURCE:
            remaining, discharged = linter.discharge_literature_axiom(name, row["findings"])
            admitted_findings.extend({"file": name, "name": linter.LITERATURE_FILE_INDEX[name],
                                      "registry_sha256": admission["source_report_contract"]["registry_sha256"],
                                      "finding": item} for item in discharged)
            if itemize:
                for finding in remaining:
                    require(finding["severity"] == "review" or finding["token"] in ITEMIZED_SOURCE_TOKENS,
                            f"Source-lint rejection cannot be itemized: {name}: {finding['token']}")
                    (reproduced_rejections if finding["severity"] == "reject" else reproduced_reviews).append(
                        dict(file=name, **finding))
            else:
                require(remaining == [], f"Source-lint findings were not discharged: {name}")
        entries, problems = linter.inspect_imports(project, Path(name), source, set(paths))
        imports.extend(entries)
        if name != TOOLING_SOURCE:
            require(not problems, f"Source import gate fails reproduction: {name}: {problems}")
    require(len(admitted_findings) == len(LITERATURE_NAMES) and
            sorted(item["name"] for item in admitted_findings) == sorted(LITERATURE_NAMES) and
            report.get("admitted_literature_findings") == admitted_findings,
            "Source-report exact axiom-token discharge is missing, duplicated or changed")
    require(report.get("imports") == imports, "Recorded import inventory fails exact reproduction")
    require(report["mathematical_source_rejections"] == reproduced_rejections and
            report["mathematical_source_reviews"] == reproduced_reviews,
            "Recorded rejection/review arrays fail exact reproduction")
    require(linter.source_policy_status(reproduced_rejections, reproduced_reviews) == report["status"],
            "Recorded source-lint status fails reproduction")
    result = {"profile": CACHE_POLICY, "status": report["status"],
              "linter": artifacts[SOURCE_LINTER], "report": artifacts[SOURCE_LINT_REPORT],
              "reviewed_linter_sha256": SOURCE_LINTER_SHA256,
              "reproduced_source_count": len(rows), "reproduced_import_count": len(imports),
              "scope": "Exact archived Lean sources; reviewed Python lexical/import checks reproduced; no Lean execution"}
    if itemize:
        result["itemized_findings"] = {
            "rejections": reproduced_rejections, "rejection_count": len(reproduced_rejections),
            "rejection_files": sorted({row["file"] for row in reproduced_rejections}),
            "reviews": reproduced_reviews, "review_count": len(reproduced_reviews),
            "review_files": sorted({row["file"] for row in reproduced_reviews}),
            "scope": "Rejections are exactly elab/partial elaborator-code tokens and review findings; they are listed, not discharged or approved"}
    return result


def validate_sources(library: dict, audit: dict, project: Path, inventory: dict,
                     driver_format_record: Path | None = None, admission: dict | None = None,
                     itemize: bool = False) -> dict:
    require(library["sources"] == audit["sources"],
            "Library and audit snapshots have different Lean sources")
    sources = library["sources"]
    require((project / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.19.0",
            "Local Lean toolchain pin differs")
    manifest = loads((project / "lake-manifest.json").read_text())
    require({p["name"]: p["rev"] for p in manifest["packages"]} == DEPENDENCIES,
            "Local dependency manifest differs from exact pins")
    for name, expected in sources.items():
        require((project / name).is_file(), f"Audited source missing locally: {name}")
        require(sha256((project / name).read_bytes()) == expected, f"Audited source changed locally: {name}")
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        fingerprints = [record[phase]["files"].get(name, {}).get("sha256")
                        for record in (library, audit) for phase in ("inputs", "outputs")]
        require(len(set(fingerprints)) == 1 and fingerprints[0] == sha256((project / name).read_bytes()),
                f"Build configuration differs across snapshots/current source: {name}")
    driver = validate_driver(audit, project, driver_format_record)
    require(admission is not None, "Missing independently validated literature admission")
    source_lint = validate_source_lint(library, audit, project, admission, itemize)
    current = {p.relative_to(project).as_posix(): sha256(p.read_bytes())
               for p in (project / "KltDP").rglob("*.lean")
               if is_source(p.relative_to(project).as_posix())}
    current["KltDP.lean"] = sha256((project / "KltDP.lean").read_bytes())
    unaudited = {name: value for name, value in sorted(current.items()) if name not in sources}
    modules = {name[:-5].replace("/", "."): name for name in sources
               if name not in {"KltDP.lean", TOOLING_SOURCE}}
    completeness = validate_module_completeness(project, sources, modules, inventory, reviewed_linter(project))
    return {"audited_sources": dict(sorted(sources.items())),
            "mathematical_modules": dict(sorted(modules.items())),
            "declaration_free_modules": completeness,
            "import_entry_point": "KltDP.lean", "audit_tooling_source": TOOLING_SOURCE,
            "audit_driver": driver["artifact"], "audit_driver_format": driver["format"],
            "audit_driver_explicit_format_record": driver["explicit_format_record"],
            "source_lint": source_lint,
            "unaudited_local_sources": unaudited, "current_local_source_coverage_complete": not unaudited}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", required=True, type=Path,
                        help="Original project whose retained sources and records are being qualified")
    parser.add_argument("--build-record", required=True, type=Path)
    parser.add_argument("--audit-record", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--driver-format-record", type=Path,
                        help="Explicit format and exact-byte hash record required for a historical separate-command driver")
    parser.add_argument("--canonical-resource-profile", choices=CANONICAL_RESOURCE_PROFILES,
                        default="standard26",
                        help="Exact library/audit envelope; historical literature probes remain standard26")
    parser.add_argument("--native-type-objects-before", type=Path,
                        help="Existing complete source/object observation before this audit")
    parser.add_argument("--native-type-objects-after", type=Path,
                        help="Existing matching source/object observation after this audit")
    parser.add_argument("--itemize-nonroot-failures", nargs="+", metavar="ROOT", default=None,
                        help="Scoped mode: accept an audit whose only failed declarations are partial-def "
                             "companions (_unsafe_rec) outside the dependency closure of every listed logical ROOT "
                             "and whose source-lint rejections are only elab/partial tokens; all are itemized and the "
                             "certificate status becomes " + ITEMIZED_STATUS + ". Without this flag the strict certificate is unchanged.")
    args = parser.parse_args()
    itemize_roots = args.itemize_nonroot_failures
    project = args.project.resolve()
    output = args.output.resolve()
    full_output = output.with_name(output.stem + ".records.json")
    require(not output.exists() and not full_output.exists(), "Output artifacts already exist; choose a new output path")
    library = load_record(args.build_record.resolve(), "library",
                          canonical_resource_profile=args.canonical_resource_profile)
    audit = load_record(args.audit_record.resolve(), "audit",
                        canonical_resource_profile=args.canonical_resource_profile,
                        allow_audit_rejection=itemize_roots is not None)
    admission = validate_literature_admission(library, audit, project)
    inventory = parse_inventory(record_log_lines(audit), admission,
                                None if itemize_roots is None else
                                {"roots": itemize_roots, "exit_code": audit["exit_code"]})
    sources = validate_sources(library, audit, project, inventory, args.driver_format_record, admission,
                               itemize_roots is not None)
    declaration_free = sources.pop("declaration_free_modules")
    native_types = validate_native_type_objects(library, audit, project, inventory,
        args.native_type_objects_before, args.native_type_objects_after, args.canonical_resource_profile)
    require((sources["audit_driver_format"]["format"] == NATIVE_REPORT_DRIVER_FORMAT) == (native_types is not None),
            "Inventory type encoding differs from the exact audited driver")
    full = {"schema": "klt-parsed-compiled-trust-records-v1", "records": inventory["records"],
            "source_log": audit["artifacts"]["build.log"]}
    if native_types is not None:
        full["native_type_references"] = native_types
    output.parent.mkdir(parents=True, exist_ok=True)
    full_artifact = write_json_artifact(full_output, full)
    index = [{"name": d["name"], "user_name": d["user_name"], "module": d["module"],
              "kind": d["kind"], "type_sha256": sha256(d["type"].encode()),
              "axioms": d["closure"]["transitive_axioms"]}
             for d in inventory["mathematical"] if not d["name"].startswith("_private.")]
    report = {
        "schema": "klt-compiled-audit-validation-v1",
        "validated_at": datetime.now(timezone.utc).isoformat(),
        "status": "snapshot_dependency_policy_validated" if itemize_roots is None else ITEMIZED_STATUS,
        "dependency_policy_status": inventory["summary"]["status"],
        "audit_exit_code": audit["exit_code"],
        "manuscript_completeness": "not_assessed",
        "semantic_statement_fidelity": "not_assessed",
        "scope": "Archived library snapshot and emitted compiled-environment dependency policy",
        "runtime_companion_scope": "Imported partial companion classification relies on the hash-bound compiled root policy; project companion classification is also cross-checked against inventory",
        "compiler_stage_cache_scope": "Reviewed Lean 4.19 compiler conventions, not unforgeable registration provenance; full unsafe closures retained, excluded from logical roots, and forbidden as logical dependencies",
        "unsafe_implementation_scope": "Intentionally nonlogical unsafe declarations without direct source ranges; exact-source lint is required, full closures are retained, and logical dependencies on them are forbidden",
        "parser": artifact(Path(__file__)), "lean_version": LEAN,
        "compiler_cache_policy": CACHE_POLICY,
        "dependencies": DEPENDENCIES,
        "resource_limits": resource_caps("library", args.canonical_resource_profile),
        "library_record": {k: library[k] for k in ("directory", "started_at", "completed_at", "artifacts")},
        "audit_record": {k: audit[k] for k in ("directory", "started_at", "completed_at", "artifacts")},
        "literature_admission": admission["public_evidence"],
        "sources": sources, "declaration_free_modules": declaration_free,
        "inventory_summary": inventory["summary"],
        "declaration_count": len(inventory["declarations"]),
        "public_declaration_index": index,
        "compiler_stage_cache_index": [{"name": d["name"], "module": d["module"],
                                         "owner": d["compiler_cache_owner"], "stage": d["compiler_cache_stage"],
                                         "closure_passes": d["closure"]["passes"]}
                                        for d in inventory["compiler_stage_caches"]],
        "unsafe_implementation_index": [{"name": d["name"], "module": d["module"],
                                          "kind": d["kind"], "closure_passes": d["closure"]["passes"]}
                                         for d in inventory["unsafe_implementations"]],
        "full_records": full_artifact,
    }
    if native_types is not None:
        report["native_type_references"] = native_types
    if itemize_roots is not None:
        report["itemized_nonroot_failures"] = inventory["itemized_nonroot_failures"]
        report["itemized_source_findings"] = sources["source_lint"]["itemized_findings"]
        report["itemized_scope"] = ("The whole-library dependency policy is NOT passed: the listed failed declarations "
                                    "and source findings are itemized, not approved. The listed logical roots pass the "
                                    "policy and reach none of the failures along the exported dependency edges.")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": report["status"], "output": str(output),
                      "declaration_count": report["declaration_count"],
                      "failed_declaration_count": inventory["summary"]["failed_declaration_count"],
                      "declaration_free_module_count": declaration_free["count"],
                      "unaudited_local_source_count": len(sources["unaudited_local_sources"])}))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValidationError, OSError, KeyError, TypeError, json.JSONDecodeError, ValueError) as error:
        print(f"Compiled audit validation FAILED: {error}", file=sys.stderr)
        sys.exit(1)
