#!/usr/bin/env python3
"""Validate archived VM build/trust records without executing Lean or Lake.

This certifies record consistency and the emitted dependency policy only. It
does not certify statement fidelity, inhabitance, or manuscript completion.
The complete parsed inventory is written beside --output as *.records.json.

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
NATIVE_TOOLING_SHA256 = "21e6b2d583ea6f35a0abc7a20967f74f47622fb6f13c45acdf0b1b39d0d7461f"
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
CACHE_POLICY = "lean419_logical_boundary_four_stacks_v6"
SOURCE_LINTER = "scripts/audit_sources.py"
SOURCE_LINT_REPORT = "audit/source_lint.json"
# Reviewed literal/import/source gate for the intentional v2 logical boundary.
# Changing this digest requires review of the new script, not merely a rehash.
SOURCE_LINTER_SHA256 = "e8eb9601f98de0a0730a8e2ba38cbce7b55d09ae59db2d0124818bed40722c5f"
ADMISSION_HELPER = "scripts/literature_admission.py"
ADMISSION_HELPER_SHA256 = "42380106c8e033ee53349998f99ab75e7358c87191f814e2225b0bd8b4277d85"
ADMISSION_REGISTRY = "audit/field_j2_admission.json"
ADMISSION_REGISTRY_SHA256 = "b341fef779503eac029e5543911d27851c7d12c829c28a0bc2707f61e724d997"
ADMISSION_NAME = "KltDP.Literature.Stacks.field_isJ2"
ADMISSION_MODULE = "KltDP.Literature.Stacks.FieldJ2"
ADMISSION_SOURCE = "KltDP/Literature/Stacks/FieldJ2.lean"
ADMISSION_PROBE = "audit/tooling_candidates/field_j2_admission/ExpectedFieldJ2Type.lean"
ADMISSION_SOURCE_CONTRACT = "audit/tooling_candidates/field_j2_admission/source_contract.json"
ADMISSION_ALLOWLIST = "audit/literature_allowlist.json"
UFD_HELPER = "scripts/regular_local_ufd_admission.py"
UFD_HELPER_SHA256 = "5121a9a8eb4ad9952dcd91727804e6329e6ef48c2bf9288dbc75024be4870b7f"
UFD_REGISTRY = "audit/regular_local_ufd_admission.json"
UFD_REGISTRY_SHA256 = "258ffdd90ad110c7d58572908c547e2f28efc4e3d5172597efe080df907e92ba"
UFD_NAME = "KltDP.Literature.Stacks.regularLocal_isUFD"
UFD_MODULE = "KltDP.Literature.Stacks.RegularLocalUFD"
UFD_SOURCE = "KltDP/Literature/Stacks/RegularLocalUFD.lean"
UFD_PROBE = "audit/literature_candidates/regular_local_factoriality/RegularLocalFactorialityTypeProbe.lean"
UFD_SOURCE_CONTRACT = "audit/tooling_candidates/regular_local_ufd_admission/source_contract.json"
UFD_SOURCE_CONTRACT_SHA256 = "b48d3fe86adb5af655aab23723b9bd594a5902817b68b6d50bd36c02b436aec1"
UFD_COMPILED_EXPRESSION_SHA256 = "42fd8a7aafee320f2d932501c94abc20579708ed6598fdb605a62e2a4dfcac3e"
UFD_COMPILED_EXPRESSION = "audit/literature_candidates/regular_local_factoriality/compiled_probe_expression.json"
PROPER_NAME = "KltDP.Literature.Stacks.properCohomology_finite"
PROPER_MODULE = "KltDP.Literature.Stacks.ProperCohomologyFinite"
PROPER_SOURCE = "KltDP/Literature/Stacks/ProperCohomologyFinite.lean"
PROPER_HELPER = "scripts/proper_cohomology_admission.py"
PROPER_HELPER_SHA256 = "296ee799c66cb09f49ba71710303d6c482f6a6ec580d1305e13f578e970a7f26"
PROPER_REGISTRY = "audit/proper_cohomology_admission.json"
PROPER_REGISTRY_SHA256 = "0639cd7244af87b8b102eab28a43916650207b7b9c8ad8d563c2ad81aea20dde"
CURVE_NAME = "KltDP.Literature.Stacks.proper_curve_tensor_degree_literal"
CURVE_MODULE = "KltDP.Literature.Stacks.CurveTensorDegreeLiteral"
CURVE_SOURCE = "KltDP/Literature/Stacks/CurveTensorDegreeLiteral.lean"
CURVE_HELPER = "scripts/curve_tensor_degree_admission.py"
CURVE_HELPER_SHA256 = "780d1284127439082505ee4cfc243a786b6b2f913d6da4a735c67e5c88f8abe6"
CURVE_REGISTRY = "audit/curve_tensor_degree_admission.json"
CURVE_REGISTRY_SHA256 = "436db9c3a61f6db0f9adc818ade10cd7abae36d1f11b62be4764e65228f0e635"
# Production copies of the probe sources live under audit/ (the source lint rejects
# `elab` under KltDP/); they were compiled on the dev project at the snapshot paths.
CURVE_EXPECTED_PROBE = "audit/literature_candidates/curve_tensor_degree/probes/CurveTensorDegreeExpectedType.lean"
CURVE_EXPECTED_PROBE_SNAPSHOT = "KltDP/AdmissionProbe/CurveTensorDegreeExpectedType.lean"
CURVE_EXPECTED_PROBE_MODULE = "KltDP.AdmissionProbe.CurveTensorDegreeExpectedType"
CURVE_NO_NEW_AXIOM_PROBE = "audit/literature_candidates/curve_tensor_degree/probes/CurveTensorDegreeNoNewAxiom.lean"
CURVE_NO_NEW_AXIOM_PROBE_SNAPSHOT = "KltDP/AdmissionProbe/CurveTensorDegreeNoNewAxiom.lean"
CURVE_NO_NEW_AXIOM_PROBE_MODULE = "KltDP.AdmissionProbe.CurveTensorDegreeNoNewAxiom"
# Both fourth-entry probes were single-module `lake build` runs on the dedicated
# dev runner; its cgroup caps differ from the production profiles and apply to
# these two roles only, never to the library or audit records.
CAPS128CPU16 = {"cpu.max": "1600000 100000", "memory.max": "137438953472",
                "memory.swap.max": "0"}
CURVE_PROBE_RESOURCE_PROFILE = "dev128cpu16"
CURVE_PROBE_ROLES = {"curve_tensor_degree_type_probe": ["lake", "build", CURVE_EXPECTED_PROBE_MODULE],
                     "curve_tensor_degree_no_new_axiom_probe": ["lake", "build", CURVE_NO_NEW_AXIOM_PROBE_MODULE]}
LITERATURE_NAMES = [ADMISSION_NAME, UFD_NAME, PROPER_NAME, CURVE_NAME]
DECLARATION_KINDS = {"axiom", "definition", "theorem", "opaque", "quotient_primitive",
                     "inductive", "constructor", "recursor"}
TAGS = {"KLT_TRUST_INVENTORY_BEGIN", "KLT_TRUST_DECL",
        "KLT_TRUST_INVENTORY_END", "KLT_TRUST_AUDIT", "KLT_TRUST_FAILURE"}
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
    require(role in {"library", "audit", "field_j2_type_probe", "regular_local_ufd_type_probe"} or
            role in CURVE_PROBE_ROLES, "Unknown build-record role")
    if role in CURVE_PROBE_ROLES:
        require(canonical_resource_profile == CURVE_PROBE_RESOURCE_PROFILE,
                "Curve-tensor-degree probes were built under the dev128cpu16 lane profile only")
        return CAPS128CPU16
    require(canonical_resource_profile in CANONICAL_RESOURCE_PROFILES,
            "Unknown canonical resource profile")
    require(role in {"library", "audit"} or canonical_resource_profile == "standard26",
            "Historical literature type probes require the original standard26 profile")
    return CAPS if canonical_resource_profile == "standard26" else CAPS256CPU4


def load_record(path: Path, role: str, *, canonical_resource_profile: str = "standard26") -> dict:
    expected_caps = resource_caps(role, canonical_resource_profile)
    require(path.is_dir(), f"{role}: missing build record directory: {path}")
    for name in RECORD_FILES:
        require((path / name).is_file(), f"{role}: missing {name}")
    require((path / "exit_code.txt").read_text().strip() == "0", f"{role}: exit was not zero")
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
    require(role in {"library", "audit", "field_j2_type_probe", "regular_local_ufd_type_probe"} or
            role in CURVE_PROBE_ROLES, "Unknown build-record role")
    expected_argv = ({"library": ["lake", "build", "KltDP", TOOLING_MODULE],
                      "audit": ["lake", "env", "lean", AUDIT_DRIVER],
                      "field_j2_type_probe": ["lake", "env", "lean", ADMISSION_PROBE],
                      "regular_local_ufd_type_probe": ["lake", "env", "lean", UFD_PROBE],
                      **CURVE_PROBE_ROLES}[role])
    require(argv == expected_argv, f"{role}: unexpected command or targets: {argv}")
    require(shlex.split((path / "command.sh").read_text()) == expected_argv,
            f"{role}: command.sh differs from cgroup command")
    start = (path / "started_at.txt").read_text().strip()
    end = (path / "completed_at.txt").read_text().strip()
    require(datetime.fromisoformat(start.replace("Z", "+00:00")) <=
            datetime.fromisoformat(end.replace("Z", "+00:00")), f"{role}: invalid timestamps")
    return {"directory": str(path.resolve()), "inputs": before, "outputs": after,
            "sources": sources, "cgroup": cgroup, "started_at": start, "completed_at": end,
            "log_path": str((path / "build.log").resolve()),
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


def parse_inventory(log: str | Iterable[str], admission: dict) -> dict:
    require(isinstance(admission.get("entries"), list) and
            all(isinstance(entry, dict) and isinstance(entry.get("entry"), dict)
                for entry in admission["entries"]) and
            [entry["entry"].get("name") for entry in admission["entries"]] == LITERATURE_NAMES,
            "Inventory requires both independently validated admission contracts")
    records = []
    lines = log.splitlines() if isinstance(log, str) else log
    for line_number, line in enumerate(lines, 1):
        match = re.search(r"\b(KLT_TRUST_[A-Z_]+)\b", line)
        if match is None:
            continue
        tag = match.group(1)
        require(tag in TAGS, f"Unknown trust tag on line {line_number}: {tag}")
        payload = loads(line[match.end():].strip())
        require(isinstance(payload, dict), f"Non-object trust payload on line {line_number}")
        records.append({"tag": tag, "log_line": line_number, "payload": payload})
    require(records, "No compiled trust records in audit log")
    grouped = {tag: [r for r in records if r["tag"] == tag] for tag in TAGS}
    require(not grouped["KLT_TRUST_FAILURE"], "Audit emitted KLT_TRUST_FAILURE")
    for tag in ("KLT_TRUST_INVENTORY_BEGIN", "KLT_TRUST_INVENTORY_END", "KLT_TRUST_AUDIT"):
        require(len(grouped[tag]) == 1, f"Expected exactly one {tag}")
    declarations = [r["payload"] for r in grouped["KLT_TRUST_DECL"]]
    require([r["tag"] for r in records] == ["KLT_TRUST_INVENTORY_BEGIN"] +
            ["KLT_TRUST_DECL"] * len(declarations) +
            ["KLT_TRUST_INVENTORY_END", "KLT_TRUST_AUDIT"],
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
            "Literature lists differ from the two exact externally reviewed admissions")
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
        approved["helper"].verify_declared_axiom(approved["entry"], declarations)
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
    require(summary.get("status") == "dependency_policy_passed" and
            summary.get("failed_declaration_count") == 0, "No successful dependency-policy summary")
    require(string_set(summary.get("transitive_axioms"), "Summary axioms") == all_axioms,
            "Summary axiom set differs from declaration closures")
    require(summary.get("manuscript_completeness") == "not_assessed_by_dependency_audit",
            "Unexpected semantic-completion claim in audit record")
    return {"records": records, "begin": begin, "summary": summary, "declarations": declarations,
            "mathematical": mathematical, "companions": companions, "tooling": tooling,
            "compiler_stage_caches": caches, "unsafe_implementations": unsafe_implementations}


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


def validate_field_j2_admission(library: dict, audit: dict, project: Path) -> dict:
    """Validate one literal reviewed axiom; no Lean or arbitrary Python is run.

    The externally pinned helper is executed from captured bytes. The probe
    predates the axiom and has its own complete, independently pinned build
    evidence. Its historical missing non-Lean evidence remains explicit; all
    meaning/evidence files must occur in the new production snapshots.
    """
    for label, digest in (("helper", ADMISSION_HELPER_SHA256),
                          ("registry", ADMISSION_REGISTRY_SHA256)):
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) is not None,
                f"Admission {label} has no externally reviewed digest")
    captured, artifacts = {}, {}

    def bind(name, expected=None):
        data, info = bind_admission_artifact(library, audit, project, name, expected)
        if name in captured:
            require(data == captured[name], f"Admission artifact changed during validation: {name}")
        captured[name], artifacts[name] = data, info
        return data

    helper_bytes = bind(ADMISSION_HELPER, ADMISSION_HELPER_SHA256)
    registry_bytes = bind(ADMISSION_REGISTRY, ADMISSION_REGISTRY_SHA256)
    helper = ModuleType("_klt_reviewed_field_j2_admission")
    helper.__file__ = str(project / ADMISSION_HELPER)
    exec(compile(helper_bytes, helper.__file__, "exec"), helper.__dict__)
    require(helper.REVIEWED_REGISTRY_SHA256 == ADMISSION_REGISTRY_SHA256 and
            helper.NAME == ADMISSION_NAME and helper.MODULE == ADMISSION_MODULE and
            helper.SOURCE == ADMISSION_SOURCE and helper.REGISTRY_PATH == ADMISSION_REGISTRY and
            helper.FOUNDATIONS == FOUNDATIONS, "Admission helper's external contract differs")
    entry = helper.load_reviewed_registry(registry_bytes, ADMISSION_REGISTRY_SHA256)
    for binding in entry["meaning_bindings"]:
        bind(binding["path"], binding["sha256"])
    probe_spec = entry["expected_type_probe"]
    bind(probe_spec["source_path"], probe_spec["source_sha256"])
    helper.verify_meaning_bytes(entry, lambda name: captured[name])
    source_bytes = bind(ADMISSION_SOURCE, entry["source_sha256"])
    require(library["sources"].get(ADMISSION_SOURCE) == audit["sources"].get(ADMISSION_SOURCE) ==
            entry["source_sha256"], "Approved axiom is absent from the compiled mathematical snapshot")
    evidence_bytes = bind(probe_spec["compiled_evidence_path"], probe_spec["compiled_evidence_sha256"])
    review_bytes = bind(entry["root_review_evidence_path"], entry["root_review_evidence_sha256"])
    helper.verify_evidence_bytes(entry, evidence_bytes, review_bytes)
    evidence = loads(evidence_bytes.decode("utf-8"))
    review = loads(review_bytes.decode("utf-8"))
    require(isinstance(evidence, dict) and isinstance(review, dict), "Malformed admission evidence")
    require(evidence.get("schema") == "klt-field-j2-type-probe-evidence-v1" and
            evidence.get("status") == "axiom_free_type_probe_succeeded" and
            type(evidence.get("exit_code")) is int and evidence["exit_code"] == 0 and
            evidence.get("no_axiom_declaration_observed_or_created") is True,
            "Independent probe did not establish its axiom-free type contract")
    require(evidence.get("build_record_path") == probe_spec["build_record_path"] and
            evidence.get("probe_source_path") == probe_spec["source_path"] and
            evidence.get("probe_source_sha256") == probe_spec["source_sha256"] and
            evidence.get("raw_type_expression_sha256") == entry["type_expression_sha256"] and
            evidence.get("printed_type_sha256") == entry["printed_type_sha256"],
            "Probe evidence does not match reviewed source/build/type")
    require(isinstance(evidence.get("record"), dict), "Independent probe type record missing")
    helper.verify_expected_probe(entry, evidence["record"])
    require(isinstance(evidence.get("artifacts"), dict) and
            set(evidence["artifacts"]) == set(RECORD_FILES), "Probe build evidence is incomplete")
    for filename in RECORD_FILES:
        name = probe_spec["build_record_path"] + "/" + filename
        expected = evidence["artifacts"][filename]
        require(isinstance(expected, dict) and set(expected) == {"path", "bytes", "sha256"} and
                expected["path"] == name and type(expected["bytes"]) is int,
                f"Malformed probe evidence artifact: {filename}")
        data = bind(name, expected["sha256"])
        require(len(data) == expected["bytes"], f"Probe evidence size mismatch: {filename}")
    probe = load_record(project / probe_spec["build_record_path"], "field_j2_type_probe")
    for filename in RECORD_FILES:
        require(probe["artifacts"][filename] == artifacts[probe_spec["build_record_path"] + "/" + filename],
                f"Probe evidence changed while loading: {filename}")
    build_id = evidence.get("build_id")
    require(isinstance(build_id, str) and re.fullmatch(r"[0-9]{8}T[0-9]{6}Z-[0-9]+", build_id) and
            probe["cgroup"].get("cgroup", "").endswith("/klt-build-" + build_id + ".scope"),
            "Independent probe build identity differs")
    require(datetime.fromisoformat(probe["completed_at"].replace("Z", "+00:00")) <=
            datetime.fromisoformat(library["started_at"].replace("Z", "+00:00")),
            "Independent expected-type probe must precede the library build")
    require(ADMISSION_SOURCE not in probe["sources"] and
            ADMISSION_SOURCE not in probe["inputs"]["files"] and
            ADMISSION_SOURCE not in probe["outputs"]["files"],
            "Independent type probe snapshot already contains the admitted axiom")
    for phase in ("inputs", "outputs"):
        require(probe[phase]["files"].get(ADMISSION_PROBE, {}).get("sha256") == probe_spec["source_sha256"] and
                probe[phase]["files"].get(ADMISSION_PROBE, {}).get("bytes") == len(captured[ADMISSION_PROBE]),
                "Independent probe source differs from its compiled snapshot")
    probe_rows = []
    for line in record_log_lines(probe):
        match = re.search(r"\bKLT_EXPECTED_FIELD_J2_TYPE\b", line)
        if match:
            require(line.startswith("KLT_EXPECTED_FIELD_J2_TYPE "), "Unexpected type-probe log marker")
            probe_rows.append(loads(line[match.end():].strip()))
    require(probe_rows == [evidence["record"]], "Expected exactly one matching independent type-probe record")
    helper.verify_expected_probe(entry, probe_rows[0])
    require(review.get("schema") == "klt-field-j2-typed-review-v1" and
            review.get("status") == "independent_type_contract_review_passed_admission_not_activated" and
            review.get("build_id") == build_id and review.get("expected_qualified_name") == ADMISSION_NAME and
            review.get("probe_evidence_sha256") == sha256(evidence_bytes) and
            review.get("universe_parameters") == entry["universe_parameters"] and
            review.get("raw_type_expression_sha256") == entry["type_expression_sha256"] and
            review.get("printed_type_sha256") == entry["printed_type_sha256"] and
            review.get("no_extra_outer_binders") is True and
            review.get("no_surface_or_dimension_or_characteristic_hypothesis") is True,
            "Independent typed review does not match the validated probe contract")
    require(review.get("outer_binders") == [
                {"name": "k", "kind": "explicit", "type": "Type u"},
                {"name": "instField", "kind": "instance_implicit", "type": "Field.{u} k"}] and
            review.get("actual_instance_expression") ==
                "EuclideanDomain.toCommRing (Field.toEuclideanDomain instField)" and
            review.get("instance_source_review", {}).get("mathlib_commit") == DEPENDENCIES["mathlib"],
            "Typed review has a different telescope or field-instance projection")
    require(review.get("source_contract_path") == ADMISSION_SOURCE_CONTRACT,
            "Typed review identifies an unexpected source contract")
    contract_bytes = bind(ADMISSION_SOURCE_CONTRACT, review.get("source_contract_sha256"))
    contract = loads(contract_bytes.decode("utf-8"))
    require(contract.get("schema") == "klt-field-j2-source-contract-v1" and
            contract.get("proposed_path") == ADMISSION_SOURCE and
            contract.get("proposed_module") == ADMISSION_MODULE and
            contract.get("qualified_name") == ADMISSION_NAME and
            contract.get("source_sha256") == entry["source_sha256"] and
            contract.get("axiom_finding") == entry["axiom_finding"] and
            contract.get("utf8_source", "").encode("utf-8") == source_bytes,
            "Actual axiom source differs from independently reviewed source text")
    in_probe, local_only = [], []
    for binding in entry["meaning_bindings"]:
        name = binding["path"]
        if name in probe["inputs"]["files"] or name in probe["outputs"]["files"]:
            for phase in ("inputs", "outputs"):
                info = probe[phase]["files"].get(name, {})
                require(info.get("sha256") == binding["sha256"] and
                        type(info.get("bytes")) is int and info["bytes"] == len(captured[name]),
                        f"Meaning source differs from independent probe snapshot: {name}")
            in_probe.append(binding)
        else:
            require(not is_source(name), f"Mathematical meaning source absent from independent probe: {name}")
            local_only.append(binding)
    require(review.get("meaning_bindings_present_in_probe_inputs_and_outputs") == in_probe and
            review.get("meaning_bindings_rehashed_locally_not_in_probe_manifest") == local_only,
            "Historical probe source coverage differs from the exact typed review")
    source_contract = {"registry_path": ADMISSION_REGISTRY,
                       "registry_sha256": ADMISSION_REGISTRY_SHA256,
                       "helper_path": ADMISSION_HELPER, "helper_sha256": ADMISSION_HELPER_SHA256,
                       "entry_name": ADMISSION_NAME,
                       "type_expression_sha256": entry["type_expression_sha256"],
                       "printed_type_sha256": entry["printed_type_sha256"]}
    return {"helper": helper, "entry": entry, "source_report_contract": source_contract,
            "public_evidence": {"policy": CACHE_POLICY, "entry": entry,
                                "source_report_contract": source_contract,
                                "artifacts": artifacts, "probe_build_id": build_id,
                                "probe_record": evidence["record"],
                                "scope": "Literal field-J2 admission and exact evidence/snapshot consistency; local use-site and manuscript semantic completion are not assessed"}}


def validate_regular_local_ufd_admission(library: dict, audit: dict, project: Path) -> dict:
    """Validate the second literal statement against its pre-admission VM probe.

    The old field-J2 helper, registry and evidence contract remain independent.
    Only externally pinned Python is loaded; the Lean probe is replayed as data.
    """
    for label, digest in (("helper", UFD_HELPER_SHA256), ("registry", UFD_REGISTRY_SHA256),
                          ("source contract", UFD_SOURCE_CONTRACT_SHA256),
                          ("compiled expression", UFD_COMPILED_EXPRESSION_SHA256)):
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) is not None,
                f"Regular-local-UFD {label} has no externally reviewed digest")
    captured, artifacts = {}, {}

    def bind(name, expected=None):
        data, info = bind_admission_artifact(library, audit, project, name, expected)
        if name in captured:
            require(data == captured[name], f"UFD artifact changed during validation: {name}")
        captured[name], artifacts[name] = data, info
        return data

    helper_bytes = bind(UFD_HELPER, UFD_HELPER_SHA256)
    registry_bytes = bind(UFD_REGISTRY, UFD_REGISTRY_SHA256)
    helper = ModuleType("_klt_reviewed_regular_local_ufd_admission")
    helper.__file__ = str(project / UFD_HELPER)
    exec(compile(helper_bytes, helper.__file__, "exec"), helper.__dict__)
    require(helper.REVIEWED_REGISTRY_SHA256 == UFD_REGISTRY_SHA256 and
            helper.NAME == UFD_NAME and helper.MODULE == UFD_MODULE and
            helper.SOURCE == UFD_SOURCE and helper.REGISTRY_PATH == UFD_REGISTRY and
            helper.FOUNDATIONS == FOUNDATIONS, "UFD helper's external contract differs")
    entry = helper.load_reviewed_registry(registry_bytes, UFD_REGISTRY_SHA256)
    for binding in entry["meaning_bindings"]:
        bind(binding["path"], binding["sha256"])
    probe_spec = entry["expected_type_probe"]
    require(probe_spec["source_path"] == UFD_PROBE, "Unexpected UFD probe source path")
    bind(UFD_PROBE, probe_spec["source_sha256"])
    helper.verify_meaning_bytes(entry, lambda name: captured[name])
    source_bytes = bind(UFD_SOURCE, entry["source_sha256"])
    require(library["sources"].get(UFD_SOURCE) == audit["sources"].get(UFD_SOURCE) ==
            entry["source_sha256"], "UFD axiom is absent from the compiled mathematical snapshot")
    evidence_bytes = bind(probe_spec["compiled_evidence_path"], probe_spec["compiled_evidence_sha256"])
    review_bytes = bind(entry["root_review_evidence_path"], entry["root_review_evidence_sha256"])
    helper.verify_evidence_bytes(entry, evidence_bytes, review_bytes)
    evidence = loads(evidence_bytes.decode("utf-8"))
    review = loads(review_bytes.decode("utf-8"))
    require(isinstance(evidence, dict) and isinstance(review, dict), "Malformed UFD evidence")
    require(evidence.get("schema") == "klt-regular-local-ufd-type-probe-evidence-v1" and
            evidence.get("status") == "axiom_free_type_probe_succeeded" and
            type(evidence.get("exit_code")) is int and evidence["exit_code"] == 0 and
            evidence.get("no_axiom_declaration_observed_or_created") is True,
            "UFD probe did not establish its axiom-free type contract")
    require(evidence.get("build_record_path") == probe_spec["build_record_path"] and
            evidence.get("probe_source_path") == UFD_PROBE and
            evidence.get("probe_source_sha256") == probe_spec["source_sha256"] and
            evidence.get("raw_type_expression_sha256") == entry["type_expression_sha256"] and
            evidence.get("printed_type_sha256") == entry["printed_type_sha256"],
            "UFD probe evidence differs from reviewed source/build/type")
    require(isinstance(evidence.get("record"), dict), "UFD probe type record missing")
    helper.verify_expected_probe(entry, evidence["record"])
    expression_bytes = bind(UFD_COMPILED_EXPRESSION, UFD_COMPILED_EXPRESSION_SHA256)
    require(loads(expression_bytes.decode("utf-8")) == evidence["record"],
            "UFD standalone compiled expression differs from probe evidence")
    require(isinstance(evidence.get("artifacts"), dict) and
            set(evidence["artifacts"]) == set(RECORD_FILES), "UFD probe build evidence is incomplete")
    for filename in RECORD_FILES:
        name = probe_spec["build_record_path"] + "/" + filename
        expected = evidence["artifacts"][filename]
        require(isinstance(expected, dict) and set(expected) == {"path", "bytes", "sha256"} and
                expected["path"] == name and type(expected["bytes"]) is int,
                f"Malformed UFD probe artifact: {filename}")
        data = bind(name, expected["sha256"])
        require(len(data) == expected["bytes"], f"UFD probe evidence size mismatch: {filename}")
    probe = load_record(project / probe_spec["build_record_path"], "regular_local_ufd_type_probe")
    for filename in RECORD_FILES:
        require(probe["artifacts"][filename] == artifacts[probe_spec["build_record_path"] + "/" + filename],
                f"UFD probe evidence changed while loading: {filename}")
    build_id = evidence.get("build_id")
    require(isinstance(build_id, str) and re.fullmatch(r"[0-9]{8}T[0-9]{6}Z-[0-9]+", build_id) and
            probe["cgroup"].get("cgroup", "").endswith("/klt-build-" + build_id + ".scope"),
            "UFD probe build identity differs")
    require(datetime.fromisoformat(probe["completed_at"].replace("Z", "+00:00")) <=
            datetime.fromisoformat(library["started_at"].replace("Z", "+00:00")),
            "UFD expected-type probe must precede the library build")
    require(UFD_SOURCE not in probe["sources"] and
            UFD_SOURCE not in probe["inputs"]["files"] and UFD_SOURCE not in probe["outputs"]["files"],
            "UFD probe snapshot already contains the new admitted axiom")
    for phase in ("inputs", "outputs"):
        info = probe[phase]["files"].get(UFD_PROBE, {})
        require(info.get("sha256") == probe_spec["source_sha256"] and
                type(info.get("bytes")) is int and info["bytes"] == len(captured[UFD_PROBE]),
                "UFD probe source differs from its compiled snapshot")
    probe_rows = []
    for line in record_log_lines(probe):
        match = re.search(r"\bKLT_EXPECTED_REGULAR_LOCAL_FACTORIALITY_TYPE\b", line)
        if match:
            require(line.startswith("KLT_EXPECTED_REGULAR_LOCAL_FACTORIALITY_TYPE "),
                    "Unexpected UFD type-probe log marker")
            probe_rows.append(loads(line[match.end():].strip()))
    require(probe_rows == [evidence["record"]], "Expected exactly one matching UFD type-probe record")
    helper.verify_expected_probe(entry, probe_rows[0])
    require(review.get("schema") == "klt-regular-local-factoriality-compiled-type-independent-review-v1" and
            review.get("verdict") == "pass_prerequisite_type_and_conditional_adapter_review_only" and
            review.get("literature_admitted") is False and
            review.get("unconditional_factoriality_proved") is False and
            review.get("checked_export") == evidence["record"],
            "Independent UFD typed review differs from the prerequisite probe contract")
    require(review.get("probe_source") == {"path": UFD_PROBE, "bytes": len(captured[UFD_PROBE]),
                                           "sha256": probe_spec["source_sha256"]},
            "Independent UFD typed review has different probe bytes")
    build_review = review.get("build", {})
    require(build_review.get("id") == build_id and
            build_review.get("directory") == probe_spec["build_record_path"] and
            type(build_review.get("exit_code")) is int and build_review["exit_code"] == 0 and
            build_review.get("started_at") == probe["started_at"] and
            build_review.get("completed_at") == probe["completed_at"] and
            build_review.get("command") == "lake env lean " + UFD_PROBE and
            build_review.get("input_output_identical") is True and
            captured[probe_spec["build_record_path"] + "/inputs.json"] ==
            captured[probe_spec["build_record_path"] + "/outputs.json"],
            "UFD typed review identifies a different or mutated probe build")
    expected_hashes = {key: sha256(evidence["record"][key].encode("utf-8"))
                       for key in ("type_expression", "type", "adapter_type_expression", "adapter_type")}
    require(review.get("checked_expression_hashes") == expected_hashes,
            "UFD typed review expression hashes differ")
    require(build_review.get("verified_dependencies") == probe["inputs"]["verified_dependencies"] and
            build_review.get("lean_version") == probe["inputs"]["lean_version"]["stdout"].strip(),
            "UFD typed review dependency pins differ")
    reviewed_records = build_review.get("records")
    require(isinstance(reviewed_records, list) and reviewed_records and
            len({row.get("path") for row in reviewed_records}) == len(reviewed_records),
            "UFD typed review record list is missing or duplicated")
    for row in reviewed_records:
        require(isinstance(row, dict) and set(row) == {"path", "bytes", "sha256"} and
                type(row["bytes"]) is int and
                row in list(evidence["artifacts"].values()), "UFD typed review record differs")
    source_contract_bytes = bind(UFD_SOURCE_CONTRACT, UFD_SOURCE_CONTRACT_SHA256)
    contract = loads(source_contract_bytes.decode("utf-8"))
    require(isinstance(contract, dict) and
            contract.get("schema") == "klt-regular-local-ufd-source-contract-v1" and
            contract.get("proposed_path") == UFD_SOURCE and contract.get("proposed_module") == UFD_MODULE and
            contract.get("qualified_name") == UFD_NAME and
            contract.get("source_sha256") == entry["source_sha256"] and
            contract.get("axiom_finding") == entry["axiom_finding"] and
            contract.get("utf8_source", "").encode("utf-8") == source_bytes,
            "UFD actual source differs from the reviewed literal source contract")
    in_probe, local_only = [], []
    for binding in entry["meaning_bindings"]:
        name = binding["path"]
        if name in probe["inputs"]["files"] or name in probe["outputs"]["files"]:
            for phase in ("inputs", "outputs"):
                info = probe[phase]["files"].get(name, {})
                require(info.get("sha256") == binding["sha256"] and
                        type(info.get("bytes")) is int and info["bytes"] == len(captured[name]),
                        f"UFD meaning source differs from probe snapshot: {name}")
            in_probe.append(binding)
        else:
            require(not is_source(name), f"UFD mathematical meaning source absent from probe: {name}")
            local_only.append(binding)
    for binding in review.get("project_source_pins", []):
        require(isinstance(binding, dict) and binding.get("matches_vm_input_and_output") is True,
                "Malformed UFD reviewed project source binding")
        name = binding.get("path")
        data = bind(name, binding.get("sha256"))
        require(type(binding.get("bytes")) is int and len(data) == binding["bytes"],
                "UFD reviewed project source size differs")
        for phase in ("inputs", "outputs"):
            require(probe[phase]["files"].get(name, {}).get("sha256") == binding["sha256"] and
                    probe[phase]["files"].get(name, {}).get("bytes") == binding["bytes"],
                    "UFD reviewed project source differs from probe snapshot")
    source_contract = {"registry_path": UFD_REGISTRY, "registry_sha256": UFD_REGISTRY_SHA256,
                       "helper_path": UFD_HELPER, "helper_sha256": UFD_HELPER_SHA256,
                       "entry_name": UFD_NAME, "type_expression_sha256": entry["type_expression_sha256"],
                       "printed_type_sha256": entry["printed_type_sha256"]}
    return {"helper": helper, "entry": entry, "source_report_contract": source_contract,
            "public_evidence": {"policy": CACHE_POLICY, "entry": entry,
                                "source_report_contract": source_contract, "artifacts": artifacts,
                                "probe_build_id": build_id, "probe_record": evidence["record"],
                                "meaning_bindings_present_in_probe": in_probe,
                                "meaning_bindings_local_only": local_only,
                                "scope": "Literal Stacks 0AG0 admission and exact evidence/snapshot consistency; geometric use sites and manuscript completion are not assessed"}}


def validate_proper_cohomology_admission(library: dict, audit: dict, project: Path) -> dict:
    """Bind the third exact entry; replay the existing isolated probe validators.

    The production parser/resource/native-type protocol remains this current
    file. Historical 96-GiB probe records keep their own reviewed validators.
    """
    import contextlib
    import io

    captured, artifacts = {}, {}

    def bind(name, expected=None):
        data, info = bind_admission_artifact(library, audit, project, name, expected)
        if name in captured:
            require(data == captured[name], "Proper-cohomology artifact changed during validation: " + name)
        captured[name], artifacts[name] = data, info
        return data

    helper_bytes = bind(PROPER_HELPER, PROPER_HELPER_SHA256)
    registry_bytes = bind(PROPER_REGISTRY, PROPER_REGISTRY_SHA256)
    helper = ModuleType("_klt_reviewed_proper_cohomology_admission")
    helper.__file__ = str(project / PROPER_HELPER)
    exec(compile(helper_bytes, helper.__file__, "exec"), helper.__dict__)
    require(helper.REVIEWED_REGISTRY_SHA256 == PROPER_REGISTRY_SHA256 and
            (helper.NAME, helper.MODULE, helper.SOURCE, helper.REGISTRY_PATH) ==
            (PROPER_NAME, PROPER_MODULE, PROPER_SOURCE, PROPER_REGISTRY) and
            helper.FOUNDATIONS == FOUNDATIONS, "Proper-cohomology helper external contract differs")
    entry = helper.load_reviewed_registry(registry_bytes, PROPER_REGISTRY_SHA256)
    for row in entry["meaning_bindings"]:
        bind(row["path"], row["sha256"])
    helper.verify_meaning_bytes(entry, lambda name: captured[name])
    bind(PROPER_SOURCE, entry["source_sha256"])
    require(library["sources"].get(PROPER_SOURCE) == audit["sources"].get(PROPER_SOURCE) ==
            entry["source_sha256"], "Literal is absent from the current compiled mathematical snapshot")
    specification = entry["qualification_evidence"]
    evidence_bytes = bind(specification["path"], specification["sha256"])
    review_bytes = bind(entry["root_review_evidence_path"], entry["root_review_evidence_sha256"])
    evidence = helper.verify_qualification_bytes(entry, evidence_bytes, review_bytes)
    for row in evidence["artifacts"]:
        require(len(bind(row["path"], row["sha256"])) == row["bytes"], "Qualification artifact size differs")
    helper.verify_control_report(captured[evidence["control_report_path"]])

    def check_pair(spec, phase):
        checker_path = spec["checker_path"]
        checker = ModuleType("_klt_proper_historical_capture_checker")
        checker.__file__ = str(project / checker_path)
        exec(compile(captured[checker_path], checker.__file__, "exec"), checker.__dict__)
        previous_argv, output = sys.argv, io.StringIO()
        try:
            sys.argv = [checker.__file__, phase, str(project / spec["build_record_path"]),
                        str(project / spec["capture_record_path"])]
            with contextlib.redirect_stdout(output):
                checker.main()
        finally:
            sys.argv = previous_argv
        result = loads(output.getvalue())
        end_path = spec["capture_record_path"] + "/completed_at.txt"
        require(datetime.fromisoformat(captured[end_path].decode().strip().replace("Z", "+00:00")) <=
                datetime.fromisoformat(library["started_at"].replace("Z", "+00:00")),
                "Proper-cohomology qualification must precede the production library build")
        return result

    pair_results = {phase: check_pair(spec, phase) for phase, spec in evidence["pairs"].items()}
    independent = check_pair(evidence["independent_ordinary"], "ordinary")
    require(independent["selected_declaration_count"] == 1 and
            independent["records"][0]["name"] ==
            "KltDP.AdmissionProbe.ProperCohomologyIndependentOrdinary.zero_add",
            "Wrong independent ordinary regression record")
    raw_records = {}
    for phase, spec in evidence["pairs"].items():
        declarations, values = {}, {}
        for line in captured[spec["capture_record_path"] + "/build.log"].decode().splitlines():
            for tag, target in (("KLT_02O6_DECL ", declarations), ("KLT_02O6_VALUE ", values)):
                if tag in line:
                    row = loads(line.split(tag, 1)[1])
                    require(row["name"] not in target, "Duplicate proper-cohomology capture record")
                    target[row["name"]] = row
        raw_records[phase] = declarations, values
        for row in entry["meaning_bindings"]:
            if is_source(row["path"]) and row["path"] != PROPER_SOURCE:
                for action in ("build_record_path", "capture_record_path"):
                    for moment in ("inputs.json", "outputs.json"):
                        snapshot = loads(captured[spec[action] + "/" + moment].decode())
                        if phase == "candidate":
                            require(row["path"] in snapshot["files"],
                                    "Mathematical meaning source absent from candidate qualification snapshot")
                        if row["path"] in snapshot["files"]:
                            require(snapshot["files"][row["path"]]["sha256"] == row["sha256"],
                                    "Meaning source differs from actual qualification snapshot: " + row["path"])
    ordinary, candidate = raw_records["ordinary"], raw_records["candidate"]
    require(all(ordinary[index][name] == candidate[index][name]
                for index in (0, 1) for name in ordinary[index]), "Original five ordinary records changed")
    helper.verify_declared_axiom(entry, list(candidate[0].values()))
    literal_value = candidate[1][PROPER_NAME]
    require(literal_value["kind"] == "axiom" and literal_value["value_present"] is False and
            literal_value["value_expression"] is None, "Literal raw capture has a value or wrong kind")
    source_contract = {"registry_path": PROPER_REGISTRY, "registry_sha256": PROPER_REGISTRY_SHA256,
                       "helper_path": PROPER_HELPER, "helper_sha256": PROPER_HELPER_SHA256,
                       "entry_name": PROPER_NAME, "type_expression_sha256": entry["type_expression_sha256"],
                       "printed_type_sha256": entry["printed_type_sha256"]}
    return {"helper": helper, "entry": entry, "source_report_contract": source_contract,
            "public_evidence": {"policy": CACHE_POLICY, "entry": entry, "source_report_contract": source_contract,
                                "artifacts": artifacts, "historical_probe_pairs": pair_results,
                                "independent_ordinary": independent,
                                "scope": "Literal Stacks 02O6 and exact qualification evidence; no vanishing, Euler truncation or manuscript completion"}}

def validate_curve_tensor_degree_admission(library: dict, audit: dict, project: Path) -> dict:
    """Bind the fourth exact entry: independent expected-type probe and packet sweep.

    Both probes are complete dev-runner build records. The expected-type probe
    never imports the literal; the no-new-axiom probe imports the whole packet,
    captures the actual axiom beside the expected type and sweeps every owned
    declaration. Nothing here is a mathematical verdict on the published lemma.
    """
    for label, digest in (("helper", CURVE_HELPER_SHA256), ("registry", CURVE_REGISTRY_SHA256)):
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) is not None,
                f"Curve-tensor-degree {label} has no externally reviewed digest")
    captured, artifacts = {}, {}

    def bind(name, expected=None):
        data, info = bind_admission_artifact(library, audit, project, name, expected)
        if name in captured:
            require(data == captured[name], "Curve-tensor-degree artifact changed during validation: " + name)
        captured[name], artifacts[name] = data, info
        return data

    helper_bytes = bind(CURVE_HELPER, CURVE_HELPER_SHA256)
    registry_bytes = bind(CURVE_REGISTRY, CURVE_REGISTRY_SHA256)
    helper = ModuleType("_klt_reviewed_curve_tensor_degree_admission")
    helper.__file__ = str(project / CURVE_HELPER)
    exec(compile(helper_bytes, helper.__file__, "exec"), helper.__dict__)
    require(helper.REVIEWED_REGISTRY_SHA256 == CURVE_REGISTRY_SHA256 and
            (helper.NAME, helper.MODULE, helper.SOURCE, helper.REGISTRY_PATH) ==
            (CURVE_NAME, CURVE_MODULE, CURVE_SOURCE, CURVE_REGISTRY) and
            helper.FOUNDATIONS == FOUNDATIONS and
            helper.EARLIER_LITERATURE == [ADMISSION_NAME, UFD_NAME, PROPER_NAME] and
            (helper.EXPECTED_PROBE_SOURCE, helper.NO_NEW_AXIOM_PROBE_SOURCE) ==
            (CURVE_EXPECTED_PROBE, CURVE_NO_NEW_AXIOM_PROBE) and
            (helper.EXPECTED_PROBE_SNAPSHOT_PATH, helper.NO_NEW_AXIOM_PROBE_SNAPSHOT_PATH) ==
            (CURVE_EXPECTED_PROBE_SNAPSHOT, CURVE_NO_NEW_AXIOM_PROBE_SNAPSHOT) and
            (helper.EXPECTED_PROBE_MODULE, helper.NO_NEW_AXIOM_PROBE_MODULE) ==
            (CURVE_EXPECTED_PROBE_MODULE, CURVE_NO_NEW_AXIOM_PROBE_MODULE),
            "Curve-tensor-degree helper external contract differs")
    entry = helper.load_reviewed_registry(registry_bytes, CURVE_REGISTRY_SHA256)
    for row in entry["meaning_bindings"]:
        bind(row["path"], row["sha256"])
    for key in ("expected_type_probe", "no_new_axiom_probe"):
        bind(entry[key]["source_path"], entry[key]["source_sha256"])
    helper.verify_meaning_bytes(entry, lambda name: captured[name])
    bind(CURVE_SOURCE, entry["source_sha256"])
    require(library["sources"].get(CURVE_SOURCE) == audit["sources"].get(CURVE_SOURCE) ==
            entry["source_sha256"], "Literal is absent from the current compiled mathematical snapshot")
    specification = entry["qualification_evidence"]
    evidence_bytes = bind(specification["path"], specification["sha256"])
    review_bytes = bind(entry["root_review_evidence_path"], entry["root_review_evidence_sha256"])
    evidence = helper.verify_qualification_bytes(entry, evidence_bytes, review_bytes)
    for row in evidence["artifacts"]:
        require(len(bind(row["path"], row["sha256"])) == row["bytes"], "Qualification artifact size differs")
    imports = re.findall(r"(?m)^import[ \t]+(\S+)", captured[CURVE_EXPECTED_PROBE].decode("utf-8"))
    require(all(module not in {CURVE_MODULE, "KltDP.Literature.Stacks.CurveTensorDegree",
                               CURVE_NO_NEW_AXIOM_PROBE_MODULE,
                               "KltDP.AdmissionProbe.CurveTensorDegreeConsumers",
                               "KltDP.Geometry.WeilRestrictionDegreeBilinear"} for module in imports),
            "Independent expected-type probe imports the literal or one of its consumers")

    def load_probe(spec, role, build_id):
        probe = load_record(project / spec["build_record_path"], role,
                            canonical_resource_profile=CURVE_PROBE_RESOURCE_PROFILE)
        for filename in RECORD_FILES:
            require(probe["artifacts"][filename] == artifacts[spec["build_record_path"] + "/" + filename],
                    "Probe evidence changed while loading: " + filename)
        require(isinstance(build_id, str) and re.fullmatch(r"[0-9]{8}T[0-9]{6}Z-[0-9]+", build_id) and
                probe["cgroup"].get("cgroup", "").endswith("/klt-build-" + build_id + ".scope"),
                "Curve-tensor-degree probe build identity differs")
        require(datetime.fromisoformat(probe["completed_at"].replace("Z", "+00:00")) <=
                datetime.fromisoformat(library["started_at"].replace("Z", "+00:00")),
                "Curve-tensor-degree probes must precede the library build")
        for phase in ("inputs", "outputs"):
            info = probe[phase]["files"].get(spec["snapshot_path"], {})
            require(info.get("sha256") == spec["source_sha256"] and
                    info.get("bytes") == len(captured[spec["source_path"]]),
                    "Probe source differs from its compiled snapshot")
            for binding in entry["meaning_bindings"]:
                if is_source(binding["path"]):
                    info = probe[phase]["files"].get(binding["path"], {})
                    require(info.get("sha256") == binding["sha256"] and
                            info.get("bytes") == len(captured[binding["path"]]),
                            "Meaning source differs from probe snapshot: " + binding["path"])
        require(probe["sources"].get(CURVE_SOURCE) == entry["source_sha256"],
                "Probe snapshot carries a different literal source")
        return probe

    expected_spec = evidence["expected_type_probe"]
    probe = load_probe(entry["expected_type_probe"], "curve_tensor_degree_type_probe", expected_spec["build_id"])
    tag = helper.EXPECTED_TAG + " "
    rows = [loads(line.split(tag, 1)[1].strip()) for line in record_log_lines(probe) if tag in line]
    require(rows == [expected_spec["record"]], "Expected exactly one matching independent type-probe record")
    helper.verify_expected_probe(entry, rows[0])
    sweep_spec = evidence["no_new_axiom_probe"]
    sweep = load_probe(entry["no_new_axiom_probe"], "curve_tensor_degree_no_new_axiom_probe", sweep_spec["build_id"])
    literal_rows, declaration_rows, summaries, printed = [], [], [], []
    # Lake replays retained messages of already-built dependencies, and long
    # `#print axioms` lists wrap onto indented continuation lines; only complete
    # messages emitted by the probe file itself are cross-checked.
    axiom_message = re.compile(re.escape(PurePosixPath(CURVE_NO_NEW_AXIOM_PROBE).name) +
                               r":\d+:\d+: '([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")

    def flush(message):
        match = axiom_message.search(message) if message else None
        if match:
            names = [name.strip() for name in (match.group(3) or "").split(",") if name.strip()]
            printed.append({"name": match.group(1), "axioms": names})

    pending = None
    for line in record_log_lines(sweep):
        for marker, target in ((helper.LITERAL_TAG + " ", literal_rows), (helper.DECL_TAG + " ", declaration_rows),
                               (helper.SUMMARY_TAG + " ", summaries)):
            if marker in line:
                target.append(loads(line.split(marker, 1)[1].strip()))
        if line[:1].isspace() and pending is not None:
            pending += " " + line.strip()
        else:
            flush(pending)
            pending = line
    flush(pending)
    require(literal_rows == [sweep_spec["literal_record"]] and declaration_rows == sweep_spec["declarations"] and
            summaries == [sweep_spec["summary"]], "No-new-axiom probe log differs from the qualification evidence")
    helper.verify_literal_capture(entry, literal_rows[0])
    helper.verify_declaration_rows(entry, declaration_rows, summaries[0])
    require(printed and all(set(row["axioms"]) <= set(helper.ALLOWED_AXIOMS) for row in printed) and
            any(row["name"] == CURVE_NAME and row["axioms"] == [CURVE_NAME] for row in printed),
            "Built-in #print axioms output is missing or lists a forbidden axiom")
    listed = {CURVE_NAME} | {name for group in ("ordinary_adapters", "consumers")
                             for module_row in entry[group] for name in module_row["declarations"]}
    require({row["name"] for row in printed} == listed and len(printed) == len(listed),
            "Built-in #print axioms output does not cover exactly the literal and every listed declaration")
    by_name = {row["name"]: row for row in declaration_rows}
    for row in printed:
        require(row["name"] in by_name and set(row["axioms"]) == set(by_name[row["name"]]["transitive_axioms"]),
                "Built-in #print axioms disagrees with the sweep: " + row["name"])
    source_contract = {"registry_path": CURVE_REGISTRY, "registry_sha256": CURVE_REGISTRY_SHA256,
                       "helper_path": CURVE_HELPER, "helper_sha256": CURVE_HELPER_SHA256,
                       "entry_name": CURVE_NAME, "type_expression_sha256": entry["type_expression_sha256"],
                       "printed_type_sha256": entry["printed_type_sha256"]}
    return {"helper": helper, "entry": entry, "source_report_contract": source_contract,
            "public_evidence": {"policy": CACHE_POLICY, "entry": entry, "source_report_contract": source_contract,
                                "artifacts": artifacts, "expected_type_probe_build_id": expected_spec["build_id"],
                                "no_new_axiom_probe_build_id": sweep_spec["build_id"],
                                "expected_type_record": rows[0], "packet_declaration_count": len(declaration_rows),
                                "scope": "Literal Stacks 0AYX and exact probe evidence; no Riemann-Roch, intersection symmetry or manuscript completion"}}

def validate_literature_admission(library: dict, audit: dict, project: Path) -> dict:
    """All four exact independent admission contracts are mandatory; no wildcard."""
    entries = [validate_field_j2_admission(library, audit, project),
               validate_regular_local_ufd_admission(library, audit, project),
               validate_proper_cohomology_admission(library, audit, project),
               validate_curve_tensor_degree_admission(library, audit, project)]
    allowlist_bytes, allowlist_artifact = bind_admission_artifact(library, audit, project, ADMISSION_ALLOWLIST)
    allowlist = loads(allowlist_bytes.decode("utf-8"))
    expected_registries = [{"path": ADMISSION_REGISTRY, "sha256": ADMISSION_REGISTRY_SHA256},
                           {"path": UFD_REGISTRY, "sha256": UFD_REGISTRY_SHA256},
                           {"path": PROPER_REGISTRY, "sha256": PROPER_REGISTRY_SHA256},
                           {"path": CURVE_REGISTRY, "sha256": CURVE_REGISTRY_SHA256}]
    require(isinstance(allowlist, dict) and
            string_set(allowlist.get("ordinary_axioms"), "Admission foundations") == FOUNDATIONS and
            allowlist.get("active_literature_axioms") == LITERATURE_NAMES and
            allowlist.get("admission_registries") == expected_registries,
            "Literature allowlist differs from the four exact registries")
    contracts = [entry["source_report_contract"] for entry in entries]
    return {"entries": entries, "source_report_contract": contracts,
            "public_evidence": {"policy": CACHE_POLICY, "entries": [entry["public_evidence"] for entry in entries],
                                "source_report_contract": contracts, "allowlist": allowlist_artifact,
                                "scope": "Four exact literal literature admissions; no additional namespace, axioms, use-site semantics or manuscript completion authorized"}}


def validate_source_lint(library: dict, audit: dict, project: Path, admission: dict) -> dict:
    """Bind and reproduce the reviewed Python source gate; never execute Lean.

    Reproduction is restricted to the archived Lean snapshot. Additional local
    project modules remain unaudited and are reported by validate_sources.
    No Python module is loaded until its bytes match the reviewed digest.
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
            report.get("status") == "source_lint_passed" and
            report.get("linter_sha256") == SOURCE_LINTER_SHA256,
            "Source-lint schema/profile/status/linter binding is invalid")
    require(report.get("proof_status") == "not_assessed_by_source_lint" and
            report.get("literature_axiom_allowlist") == LITERATURE_NAMES,
            "Source lint claims proof completion or an unauthorized literature allowlist")
    for key in ("mathematical_source_rejections", "mathematical_source_reviews", "import_policy_rejections"):
        require(report.get(key) == [], f"Source-lint admission has missing or nonempty {key}")
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

    # Loading is safe only because the script bytes above match the reviewed
    # constant. Its __main__ entry point is not invoked and no report is written.
    linter = ModuleType("_klt_reviewed_source_gate")
    linter.__file__ = str(project / SOURCE_LINTER)
    # Compile the captured, hash-checked bytes directly. Python import loaders
    # may otherwise execute a timestamp-valid .pyc that was never reviewed.
    exec(compile(artifact_bytes[SOURCE_LINTER], linter.__file__, "exec"), linter.__dict__)
    require(linter.SOURCE_POLICY_PROFILE == CACHE_POLICY, "Reviewed source-gate profile differs")
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
    require(linter.ADMISSION_HELPER_SHA256 == ADMISSION_HELPER_SHA256 and
            linter.ADMISSION_REGISTRY == ADMISSION_REGISTRY and
            linter.ADMISSION_HELPER == ADMISSION_HELPER,
            "Source-gate field-J2 admission helper contract differs")
    require(linter.UFD_ADMISSION_HELPER_SHA256 == UFD_HELPER_SHA256 and
            linter.UFD_ADMISSION_REGISTRY == UFD_REGISTRY and linter.UFD_ADMISSION_HELPER == UFD_HELPER,
            "Source-gate regular-local-UFD admission helper contract differs")
    require(linter.PROPER_ADMISSION_HELPER_SHA256 == PROPER_HELPER_SHA256 and
            linter.PROPER_ADMISSION_REGISTRY == PROPER_REGISTRY and linter.PROPER_ADMISSION_HELPER == PROPER_HELPER,
            "Source-gate proper-cohomology admission helper contract differs")
    require(linter.CURVE_ADMISSION_HELPER_SHA256 == CURVE_HELPER_SHA256 and
            linter.CURVE_ADMISSION_REGISTRY == CURVE_REGISTRY and linter.CURVE_ADMISSION_HELPER == CURVE_HELPER,
            "Source-gate curve-tensor-degree admission helper contract differs")
    imports, admitted_findings = [], []
    for row in rows:
        name = row["path"]
        source = source_texts[name]
        require(row["findings"] == linter.findings(source),
                f"Recorded source findings fail reproduction: {name}")
        if name != TOOLING_SOURCE:
            remaining = row["findings"]
            for approved in admission["entries"]:
                remaining, discharged = approved["helper"].discharge_exact_axiom_token(
                    approved["entry"], name, source.encode("utf-8"), remaining)
                contract = approved["source_report_contract"]
                admitted_findings.extend({"file": name, "name": approved["entry"]["name"],
                                         "registry_sha256": contract["registry_sha256"],
                                         "finding": item} for item in discharged)
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
    return {"profile": CACHE_POLICY, "status": "source_lint_passed",
            "linter": artifacts[SOURCE_LINTER], "report": artifacts[SOURCE_LINT_REPORT],
            "reviewed_linter_sha256": SOURCE_LINTER_SHA256,
            "reproduced_source_count": len(rows), "reproduced_import_count": len(imports),
            "scope": "Exact archived Lean sources; reviewed Python lexical/import checks reproduced; no Lean execution"}


def validate_sources(library: dict, audit: dict, project: Path, inventory: dict,
                     driver_format_record: Path | None = None, admission: dict | None = None) -> dict:
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
    source_lint = validate_source_lint(library, audit, project, admission)
    current = {p.relative_to(project).as_posix(): sha256(p.read_bytes())
               for p in (project / "KltDP").rglob("*.lean")
               if is_source(p.relative_to(project).as_posix())}
    current["KltDP.lean"] = sha256((project / "KltDP.lean").read_bytes())
    unaudited = {name: value for name, value in sorted(current.items()) if name not in sources}
    modules = {name[:-5].replace("/", "."): name for name in sources
               if name not in {"KltDP.lean", TOOLING_SOURCE}}
    represented = {d["module"] for d in inventory["mathematical"] + inventory["companions"]}
    all_inventory_modules = {d["module"] for d in inventory["declarations"]}
    archived_modules = {name[:-5].replace("/", ".") for name in sources}
    require(all_inventory_modules <= archived_modules,
            "Inventory contains declaration modules outside the archived source snapshot: " +
            ", ".join(sorted(all_inventory_modules - archived_modules)))
    require(set(modules) <= represented,
            "Library mathematical modules absent from inventory: " + ", ".join(sorted(set(modules) - represented)))
    require(represented <= set(modules) | {"KltDP"},
            "Inventory contains modules outside library snapshot: " + ", ".join(sorted(represented - set(modules) - {"KltDP"})))
    return {"audited_sources": dict(sorted(sources.items())),
            "mathematical_modules": dict(sorted(modules.items())),
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
    args = parser.parse_args()
    project = args.project.resolve()
    output = args.output.resolve()
    full_output = output.with_name(output.stem + ".records.json")
    require(not output.exists() and not full_output.exists(), "Output artifacts already exist; choose a new output path")
    library = load_record(args.build_record.resolve(), "library",
                          canonical_resource_profile=args.canonical_resource_profile)
    audit = load_record(args.audit_record.resolve(), "audit",
                        canonical_resource_profile=args.canonical_resource_profile)
    admission = validate_literature_admission(library, audit, project)
    inventory = parse_inventory(record_log_lines(audit), admission)
    sources = validate_sources(library, audit, project, inventory, args.driver_format_record, admission)
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
        "status": "snapshot_dependency_policy_validated",
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
        "sources": sources, "inventory_summary": inventory["summary"],
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
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": report["status"], "output": str(output),
                      "declaration_count": report["declaration_count"],
                      "unaudited_local_source_count": len(sources["unaudited_local_sources"])}))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValidationError, OSError, KeyError, TypeError, json.JSONDecodeError, ValueError) as error:
        print(f"Compiled audit validation FAILED: {error}", file=sys.stderr)
        sys.exit(1)
