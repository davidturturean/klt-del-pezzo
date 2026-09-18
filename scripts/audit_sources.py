#!/usr/bin/env python3
"""Lint Lean source trust boundaries; optionally emit the compiled-environment driver.

This is a source lint, never evidence that a theorem was compiled or proved.
The authoritative dependency check is KltDP.Audit.Trust on a remote clean build.
Policy v7: the `axiom` rejection is discharged only in the twenty-eight allowlisted
literature files (one axiom each); every other lexical rule is unchanged from v6.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from types import ModuleType


REJECT = {
    "sorry": "postponed proof syntax",
    "admit": "postponed proof syntax",
    "sorryAx": "postponed proof constant",
    "axiom": "axiom declarations are admitted only in the twenty-eight reviewed literature files, exactly one per file",
    "constant": "unchecked declaration requires review",
    "native_decide": "native evaluator proof path is forbidden",
    "native_eval": "native evaluator proof path is forbidden",
    "skipKernelTC": "kernel-checking override is forbidden, including debug.skipKernelTC",
    "addDeclWithoutChecking": "unchecked environment insertion is forbidden",
    "unsafe": "unsafe mathematical source declaration",
    "partial": "partial mathematical source declaration",
    "run_cmd": "unreviewed command execution can construct declarations without source ranges",
    "run_tac": "unreviewed tactic execution can construct environment declarations",
    "elab": "unreviewed elaborator extension",
    "elab_rules": "unreviewed elaborator extension",
    "macro": "unreviewed syntax expansion",
    "macro_rules": "unreviewed syntax expansion",
    "syntax": "unreviewed syntax extension",
    "initialize": "unreviewed initialization code",
    "builtin_initialize": "unreviewed initialization code",
    "addDeclCore": "direct kernel/environment insertion requires reviewed tooling",
    "modifyEnv": "direct environment mutation requires reviewed tooling",
    "setEnv": "direct environment replacement requires reviewed tooling",
    "dbg_trace": "debug interpolation can elaborate hidden term holes",
}
# Deliberately reject the full leaf-name family, including future variants.
# This is spelling-based policy, not Lean name resolution or an axiom detector.
REJECT_PREFIXES = {
    "ofReduce": "native evaluator axiom family ofReduce* is forbidden",
    "run_": "unreviewed metaprogram execution family, including run_tac and run_conv",
}
REVIEW = {
    "extern": "foreign implementation attribute; inspect its checked Lean value",
    "implemented_by": "runtime implementation substitution; inspect kernel value separately",
    "opaque": "inspect checked opaque value and semantic meaning",
    "attribute": "attribute command needs an exact reviewed form",
}
SOURCE_POLICY_PROFILE = "lean419_logical_boundary_twentyeight_admissions_v7"
REVIEWED_ATTRIBUTE_COMMANDS = (
    "attribute [local instance] MvPolynomial.gradedAlgebra",
    "attribute [local instance] Types.instFunLike Types.instConcreteCategory",
)
# A target list may continue on another line. These pinned single-token command
# starters (or EOF) terminate a reviewed one-line form for this source policy.
# The literal same-line `local instance` starter is checked separately below.
# Unknown successors require review; this is not a general Lean parser.
REVIEWED_ATTRIBUTE_FOLLOWERS = {
    "abbrev", "attribute", "axiom", "class", "def", "end", "example",
    "inductive", "instance", "namespace", "noncomputable", "nonrec",
    "opaque", "open", "partial", "private", "protected", "section",
    "set_option", "structure", "theorem", "universe", "unsafe", "variable",
}
REVIEWED_DECLARATION_ATTRIBUTES = {"simp", "ext", "reassoc"}


def mask_noncode(source: str, *, literal_findings: list[dict] | None = None) -> str:
    """Mask nested comments and strings while preserving source offsets/newlines.

    This intentionally is not a Lean parser. Interpolated string contents and
    quoted identifiers are not elaborated; the compiled audit remains necessary.
    """
    out = list(source)
    i, depth = 0, 0
    in_string = False
    string_start = 0
    string_reviewed = False
    def review(start: int, token: str, reason: str) -> None:
        if literal_findings is not None:
            literal_findings.append({"line": source.count("\n", 0, start) + 1,
                                     "column": start - source.rfind("\n", 0, start),
                                     "token": token, "severity": "review", "reason": reason})
    def blank(start: int, end: int) -> None:
        for index in range(start, end):
            if source[index] != "\n":
                out[index] = " "
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif in_string:
            if source[i] == "{" and not string_reviewed:
                review(string_start, "string_with_brace",
                       "string braces may introduce elaborated holes under contextual interpolation syntax")
                string_reviewed = True
            if source[i] == "\\" and i + 1 < len(source):
                out[i] = " "
                if source[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
            out[i:end] = " " * (end - i)
            i = end
        elif source.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif source[i] == "«":
            end = source.find("»", i + 1)
            end = len(source) if end < 0 else end + 1
            review(i, "quoted_identifier", "quoted identifiers need review; their contents are not ASCII name tokens")
            blank(i, end)
            i = end
        elif source[i] == "r" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'.")) and (
                raw := re.match(r'r(#+)?"', source[i:])):
            delimiter = '"' + (raw.group(1) or "")
            end = source.find(delimiter, i + len(raw.group()))
            end = len(source) if end < 0 else end + len(delimiter)
            review(i, "raw_string", "raw string syntax requires source review")
            blank(i, end)
            i = end
        elif source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'.")) and (
                char := re.match(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|[\\\"'rnt])|[^\\])'", source[i:])):
            end = i + len(char.group())
            review(i, "character_literal", "character literal syntax requires source review")
            blank(i, end)
            i = end
        elif source[i] == '"':
            prefix = re.search(r"[\w.]+![ \t\r\n]*$", "".join(out[:i]))
            if prefix:
                review(prefix.start(), "interpolated_string", "interpolation holes can elaborate environment-mutating terms")
            out[i] = " "
            in_string = True
            string_start = i
            string_reviewed = False
            i += 1
        else:
            i += 1
    return "".join(out)


def findings(source: str) -> list[dict]:
    result = []
    masked = mask_noncode(source, literal_findings=result)
    tokens = list(re.finditer(r"[A-Za-z_][A-Za-z0-9_'.]*", masked))
    for token in tokens:
        word = token.group().rsplit(".", 1)[-1]
        if word == "attribute":
            begin = masked.rfind("\n", 0, token.start()) + 1
            end = masked.find("\n", token.end())
            if end < 0:
                end = len(masked)
            if masked[begin:end].strip() in REVIEWED_ATTRIBUTE_COMMANDS:
                remaining = masked[end:].lstrip()
                follower = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", remaining)
                # Check original text so masking a string, quoted name or comment
                # cannot manufacture the newly reviewed two-keyword starter.
                local_instance = re.match(
                    r"local[ \t]+instance(?=\s|$)",
                    source[len(masked) - len(remaining):])
                if not remaining or local_instance is not None or (
                        follower is not None and follower.group() in REVIEWED_ATTRIBUTE_FOLLOWERS and
                        (follower.end() == len(remaining) or remaining[follower.end()].isspace())):
                    continue
        reject_reason = REJECT.get(word) or next(
            (reason for prefix, reason in REJECT_PREFIXES.items()
             if word.startswith(prefix)), None)
        if token.start() > 0 and masked[token.start() - 1] == "#" and word in {"eval", "eval!"}:
            reject_reason = "source evaluation can execute arbitrary elaborator/runtime code"
        reason = reject_reason or REVIEW.get(word)
        if reason:
            result.append({
                "line": source.count("\n", 0, token.start()) + 1,
                "column": token.start() - source.rfind("\n", 0, token.start()),
                "token": token.group(),
                "severity": "reject" if reject_reason else "review",
                "reason": reason,
            })
    for annotation in re.finditer(r"@\[[^\]]*(?:\]|$)", masked):
        inner = annotation.group()[2:-1] if annotation.group().endswith("]") else ""
        names = [name.strip() for name in inner.split(",")]
        if names and all(name in REVIEWED_DECLARATION_ATTRIBUTES for name in names):
            continue
        result.append({"line": source.count("\n", 0, annotation.start()) + 1,
                       "column": annotation.start() - source.rfind("\n", 0, annotation.start()),
                       "token": annotation.group(), "severity": "review",
                       "reason": "declaration attribute handler is not one of the reviewed pinned stock handlers"})
    return sorted(result, key=lambda row: (row["line"], row["column"]))


def source_policy_status(rejections: list, reviews: list) -> str:
    if rejections:
        return "source_lint_rejected"
    if reviews:
        return "source_policy_review_required"
    return "source_lint_passed"


def inspect_imports(root: Path, relative: Path, source: str, scanned: set[str]) -> tuple[list, list]:
    """Conservative import spelling gate; module resolution remains build-bound."""
    imports, problems = [], []
    masked = mask_noncode(source)
    covered = []
    for match in re.finditer(r"(?m)^[ \t]*import[ \t]+([^\n]+)", masked):
        if match.group(1).strip():
            covered.append((match.start(), match.end()))
        for module in match.group(1).split():
            row = {"file": relative.as_posix(), "module": module,
                   "line": source.count("\n", 0, match.start()) + 1}
            imports.append(row)
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", module):
                problems.append(dict(row, reason="unreviewed import syntax"))
                continue
            local = module.replace(".", "/") + ".lean"
            if module == "KltDP" or module.startswith("KltDP."):
                if local not in scanned:
                    problems.append(dict(row, reason="project import is not in the scanned source inventory"))
            elif module.split(".")[0] in {"Mathlib", "Lean", "Init", "Std"}:
                if (root / local).exists():
                    problems.append(dict(row, reason="local source shadows a pinned dependency module"))
            else:
                problems.append(dict(row, reason="unscanned local or unpinned dependency import"))
    # Lean's header parser is token-based: `import\nOutside.Tooling` is legal.
    # This conservative gate accepts canonical same-line imports only; it must
    # reject every other import token rather than silently omit its dependency.
    for token in re.finditer(r"(?<![A-Za-z0-9_'.])import(?![A-Za-z0-9_'.])", masked):
        if not any(start <= token.start() < end for start, end in covered):
            problems.append({"file": relative.as_posix(), "module": "<noncanonical-import>",
                             "line": source.count("\n", 0, token.start()) + 1,
                             "reason": "import token is outside an accepted same-line header form"})
    return imports, problems


def self_test() -> None:
    harmless = '/- sorry /- axiom -/ unsafe -/\n-- admit\ndef text := "sorry \\" axiom"\n'
    assert findings(harmless) == []
    bad = "theorem bad : True := by\n  exact Lean.ofReduceBool _\naxiom oracle : False\n"
    got = findings(bad)
    assert [(x["line"], x["token"]) for x in got] == [
        (2, "Lean.ofReduceBool"), (3, "axiom")]
    assert len(mask_noncode(harmless)) == len(harmless)
    assert mask_noncode(harmless).count("\n") == harmless.count("\n")
    assert findings("theorem notsorry : True := by trivial") == []
    assert findings("partial def f := f")[0]["severity"] == "reject"

    # Every dangerous leaf must be caught both unqualified and qualified,
    # including the option's actual spelling and literal-name quotations.
    rejected_spellings = [
        "skipKernelTC", "debug.skipKernelTC", "Lean.debug.skipKernelTC",
        "addDeclWithoutChecking", "Lean.addDeclWithoutChecking",
        "Lean.Environment.addDeclWithoutChecking",
        "ofReduce", "ofReduceBool", "ofReduceNat", "ofReduceFutureVariant",
        "Lean.ofReduceBool", "Lean.ofReduceNat", "_root_.Lean.ofReduceFutureVariant",
    ]
    for spelling in rejected_spellings:
        source = f"/- harmless prefix -/\n  #check {spelling}\n"
        got = findings(source)
        assert len(got) == 1, (spelling, got)
        assert (got[0]["token"], got[0]["severity"], got[0]["line"],
                got[0]["column"]) == (spelling, "reject", 2, 10), got
    for value in ("true", "false"):
        # Even a disabling override is prohibited source policy, not silently
        # accepted based on a lexer guessing the option's elaborated value.
        got = findings(f"set_option debug.skipKernelTC {value} in\n#check True")
        assert [(row["token"], row["severity"]) for row in got] == [
            ("debug.skipKernelTC", "reject")], got
    got = findings("def opts := o.setBool `debug.skipKernelTC true")
    assert [row["token"] for row in got] == ["debug.skipKernelTC"], got
    got = findings("def quoted := ``Lean.ofReduceBool")
    assert [row["token"] for row in got] == ["Lean.ofReduceBool"], got

    # Comments, strings and escaped quotes must not fabricate rejection or
    # change the location reported for the actual code after them.
    masked = (
        '/- debug.skipKernelTC /- Lean.ofReduceFutureVariant -/\n'
        '   addDeclWithoutChecking -/\n'
        '-- Lean.ofReduceBool\n'
        'def text := "debug.skipKernelTC \\" Lean.ofReduceNat"\n'
        '  #check Lean.addDeclWithoutChecking\n'
    )
    got = findings(masked)
    assert [(row["token"], row["line"], row["column"]) for row in got] == [
        ("Lean.addDeclWithoutChecking", 5, 10)], got
    assert len(mask_noncode(masked)) == len(masked)
    assert [i for i, char in enumerate(masked) if char == "\n"] == [
        i for i, char in enumerate(mask_noncode(masked)) if char == "\n"]
    for harmless_name in ("notsorry", "notofReduceBool", "safeSkipKernelTC",
                          "skipKernelTCSuffix", "addDeclWithoutCheckingLater"):
        assert findings(f"def {harmless_name} := 0") == [], harmless_name
    got = findings("opaque checked : Nat := 0")
    assert len(got) == 1 and got[0]["severity"] == "review", got
    assert source_policy_status([], got) == "source_policy_review_required"
    for entry in ("run_cmd", "run_tac", "initialize", "builtin_initialize",
                  "syntax", "elab_rules", "macro_rules", "elab", "macro",
                  "Lean.addDeclCore", "Lean.modifyEnv", "Lean.setEnv", "#eval", "#eval!"):
        assert any(row["severity"] == "reject" for row in findings(entry + " payload")), entry
        assert findings('/- ' + entry + ' -/\ndef text := "' + entry + '"') == [], entry
    for command in REVIEWED_ATTRIBUTE_COMMANDS:
        assert findings(command + " -- reviewed form\n") == []
        assert findings(command + "\nnamespace Reviewed\nend Reviewed\n") == []
        assert findings(command + "\nExtra.target"), "Multiline target extension must require review"
        assert findings(command + "\n/- gap -/ Extra.target"), "Masked comments cannot hide a target"
        assert findings(command + "\nin\ntheorem checked : True := True.intro"), "Scope wrapper is not an admitted form"
    for command in ("attribute [instance] MvPolynomial.gradedAlgebra",
                    "attribute [local instance] Other.generator",
                    REVIEWED_ATTRIBUTE_COMMANDS[0] + " extra", "attribute [evil] target"):
        assert source_policy_status([], findings(command)) == "source_policy_review_required", command
    for attr in REVIEWED_DECLARATION_ATTRIBUTES:
        assert findings(f"@[{attr}] theorem checked : True := True.intro") == []
    assert findings("@[unreviewed] theorem checked : True := True.intro")[0]["severity"] == "review"
    assert findings('/- @[unreviewed] -/ def text := "@[unreviewed]"') == []
    for source in ('#check s!"{(by run_tac pure (); exact 0 : Nat)}"',
                   '#check m!"{(by run_tac pure (); exact 0 : Nat)}"',
                   '#check m! /- token gap -/ "{(by run_tac pure (); exact 0 : Nat)}"',
                   '#check f!"{payload}"', 'dbg_trace "{payload}"; 0',
                   '#check (throwError "{(by run_tac pure (); exact 0 : Nat)}" : Lean.CoreM Unit)',
                   'Macro.trace[foo] "{(by run_tac pure (); exact 0 : Nat)}"'):
        assert findings(source), source
        assert source_policy_status([r for r in findings(source) if r["severity"] == "reject"],
                                    [r for r in findings(source) if r["severity"] == "review"]) != "source_lint_passed"
    for literal in ('\'"\'', 'r#"a"b"#', '«quote"name»', "'\\u0022'", "'\\x22'"):
        source = '#check ' + literal + '\nrun_cmd pure ()\n'
        got = findings(source)
        assert any(r['severity'] == 'review' for r in got), (source, got)
        assert any(r['token'] == 'run_cmd' and r['line'] == 2 for r in got), (source, got)
        assert len(mask_noncode(source)) == len(source)
    assert findings("def x'a' := 0") == []
    for token in ("run_conv", "Lean.run_conv", "run_future_metaprogram"):
        assert findings(token)[0]["severity"] == "reject", token
    assert findings('/- s!"hole" r#"raw"# «quote"id» \'"\' -/\n-- s!"hole"\n') == []

    # Exercise the command-line boundary, not just the token classifier. An
    # arbitrary file under Audit must not inherit Trust.lean's exemption.
    import subprocess
    from tempfile import TemporaryDirectory

    with TemporaryDirectory(prefix="klt-source-lexer-") as directory:
        root = Path(directory)
        (root / "KltDP/Audit").mkdir(parents=True)
        (root / "KltDP/Audit/Trust.lean").write_text("partial def tooling := tooling\n")
        hidden = root / "KltDP/Audit/Launder.lean"
        hidden.write_text("axiom KltDP.hidden : False\n")
        (root / "KltDP.lean").write_text("import KltDP.Audit.Launder\n")
        output = root / "report.json"
        command = [sys.executable, str(Path(__file__).resolve()), "--root", str(root),
                   "--output", str(output)]
        failed = subprocess.run(command, capture_output=True, text=True)
        assert failed.returncode == 1, (failed.returncode, failed.stdout, failed.stderr)
        report = json.loads(output.read_text())
        assert report["status"] == "source_lint_rejected", report
        assert [(row["file"], row["token"]) for row in
                report["mathematical_source_rejections"]] == [
            ("KltDP/Audit/Launder.lean", "axiom")], report
        hidden.write_text("theorem KltDP.checked : True := True.intro\n")
        passed = subprocess.run(command, capture_output=True, text=True)
        assert passed.returncode == 0, (passed.returncode, passed.stdout, passed.stderr)
        report = json.loads(output.read_text())
        assert report["status"] == "source_lint_passed", report
        assert report["proof_status"] == "not_assessed_by_source_lint", report
        assert report["mathematical_source_rejections"] == [], report
        hidden.write_text("opaque checked : Nat := 0\n")
        reviewed = subprocess.run(command, capture_output=True, text=True)
        assert reviewed.returncode == 1, reviewed.stderr
        assert json.loads(output.read_text())["status"] == "source_policy_review_required"
        hidden.write_text("import Unscanned.Attack\ntheorem checked : True := True.intro\n")
        imported = subprocess.run(command, capture_output=True, text=True)
        assert imported.returncode == 1, imported.stderr
        assert json.loads(output.read_text())["import_policy_rejections"], output.read_text()
        hidden.write_text("import /- comment -/\nUnscanned.Attack\n")
        comment_header = subprocess.run(command, capture_output=True, text=True)
        assert comment_header.returncode == 1, comment_header.stderr
        assert json.loads(output.read_text())["import_policy_rejections"], output.read_text()
        hidden.write_text("import\nUnscanned.Attack\ntheorem checked : True := True.intro\n")
        multiline = subprocess.run(command, capture_output=True, text=True)
        assert multiline.returncode == 1, multiline.stderr
        assert json.loads(output.read_text())["import_policy_rejections"], output.read_text()
        hidden.write_text("import Lean\ntheorem checked : True := True.intro\n")
        (root / "Lean.lean").write_text("axiom injected : False\n")
        shadowed = subprocess.run(command, capture_output=True, text=True)
        assert shadowed.returncode == 1, shadowed.stderr
        assert json.loads(output.read_text())["import_policy_rejections"], output.read_text()
        (root / "Lean.lean").unlink()
        hidden.write_text("theorem checked : True := True.intro\n")
        # An allowlisted literature file may declare exactly one axiom; a second one is fatal.
        literal = root / "KltDP/Literature/Stacks/FieldJ2.lean"
        literal.parent.mkdir(parents=True)
        literal.write_text("axiom KltDP.Literature.Stacks.field_isJ2 : True\n")
        admitted = subprocess.run(command, capture_output=True, text=True)
        assert admitted.returncode == 0, (admitted.returncode, admitted.stdout, admitted.stderr)
        report = json.loads(output.read_text())
        assert report["status"] == "source_lint_passed", report
        assert [(row["file"], row["name"], row["finding"]["token"]) for row in
                report["admitted_literature_findings"]] == [
            ("KltDP/Literature/Stacks/FieldJ2.lean", "KltDP.Literature.Stacks.field_isJ2", "axiom")], report
        assert report["literature_admission"]["registry_sha256"] is None, report
        literal.write_text("axiom KltDP.Literature.Stacks.field_isJ2 : True\naxiom extra : False\n")
        doubled = subprocess.run(command, capture_output=True, text=True)
        assert doubled.returncode != 0, doubled.stdout
        assert "exactly one axiom token" in doubled.stderr, doubled.stderr
        literal.write_text("theorem KltDP.Literature.Stacks.field_isJ2 : True := True.intro\n")
        missing = subprocess.run(command, capture_output=True, text=True)
        assert missing.returncode != 0, missing.stdout
        assert "exactly one axiom token" in missing.stderr, missing.stderr


def is_audit_tooling(relative: Path) -> bool:
    """Keep the lexical exemption identical to the compiled module exemption."""
    return relative.as_posix() == "KltDP/Audit/Trust.lean"


LITERATURE_REGISTRY = "audit/literature-assumptions.json"
LITERATURE_REGISTRY_SCHEMA = "klt-literature-assumptions-v7"
# Policy v7 axiom allowlist: exactly these twenty-eight source files may declare an `axiom`,
# each exactly one, the named literature admission. Canonical (lexicographic) name order. Every
# other file keeps the unconditional `axiom` rejection. This table is spelling policy; the
# compiled audit (KltDP.Audit.Trust) and the production parser bind names, modules, sources and
# types independently through the registry above.
LITERATURE_AXIOM_FILES = (
    ("KltDP/Literature/HartshorneCastelnuovoLiteral.lean",
     "KltDP.Literature.Hartshorne.castelnuovo_contraction_literal"),
    ("KltDP/Literature/Hartshorne/StrictTransformInstance.lean",
     "KltDP.Literature.Hartshorne.hasContractionLifts_instance"),
    ("KltDP/Literature/Hartshorne/HurwitzDegreeTwoInstance.lean",
     "KltDP.Literature.Hartshorne.hurwitz_degreeTwo_projectiveLine_instance"),
    ("KltDP/Literature/Hartshorne/IntegralNumericalGroup.lean",
     "KltDP.Literature.Hartshorne.integral_numerical_group_free_finite_literal"),
    ("KltDP/Literature/Hartshorne/MinimalSurfaceClassification.lean",
     "KltDP.Literature.Hartshorne.minimal_surface_classification_literal"),
    ("KltDP/Literature/Hartshorne/SurfaceProjectivity.lean",
     "KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal"),
    ("KltDP/Literature/Hartshorne/PointBlowupCohomology.lean",
     "KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal"),
    ("KltDP/Literature/Hartshorne/RuledSurfaceGenus.lean",
     "KltDP.Literature.Hartshorne.ruled_surface_genus_literal"),
    ("KltDP/Literature/Hartshorne/RuledSurfacePicard.lean",
     "KltDP.Literature.Hartshorne.ruled_surface_picard_literal"),
    ("KltDP/Literature/Hartshorne/SurfaceHodgeIndex.lean",
     "KltDP.Literature.Hartshorne.surface_hodge_index_literal"),
    ("KltDP/Literature/Hartshorne/SurfaceNakaiMoishezon.lean",
     "KltDP.Literature.Hartshorne.surface_nakai_moishezon_literal"),
    ("KltDP/Literature/Hartshorne/SurfaceRiemannRoch.lean",
     "KltDP.Literature.Hartshorne.surface_riemannRoch_literal"),
    ("KltDP/Literature/KeelCompleteSystem.lean",
     "KltDP.Literature.Keel.semiampleness_completeSystem_literal"),
    ("KltDP/Literature/Stacks/AffineMorphismCohomology.lean",
     "KltDP.Literature.Stacks.affine_morphism_cohomology_literal"),
    ("KltDP/Literature/Stacks/BlowupRegularPointAdmitted.lean",
     "KltDP.Literature.Stacks.blowupRegularPoint_literal"),
    ("KltDP/Literature/StacksPointBlowupDomination.lean",
     "KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal"),
    ("KltDP/Literature/Stacks/FieldJ2.lean",
     "KltDP.Literature.Stacks.field_isJ2"),
    ("KltDP/Literature/LipmanResolutionLiteral.lean",
     "KltDP.Literature.Stacks.lipman_resolution_of_normal_completions_literal"),
    ("KltDP/Literature/Stacks/ProperCohomologyFinite.lean",
     "KltDP.Literature.Stacks.properCohomology_finite"),
    ("KltDP/Literature/Stacks/ProperFlatFiberEuler.lean",
     "KltDP.Literature.Stacks.properFlat_fiberEuler_literal"),
    ("KltDP/Literature/ProperCurvePullbackDegreeLiteral.lean",
     "KltDP.Literature.Stacks.proper_curve_pullback_degree_literal"),
    ("KltDP/Literature/Stacks/CurveTensorDegreeLiteral.lean",
     "KltDP.Literature.Stacks.proper_curve_tensor_degree_literal"),
    ("KltDP/Literature/Stacks/RegularLocalUFD.lean",
     "KltDP.Literature.Stacks.regularLocal_isUFD"),
    ("KltDP/Literature/RegularSmoothLociLiteral.lean",
     "KltDP.Literature.Stacks.regular_smooth_loci_perfect_literal"),
    ("KltDP/Literature/SmoothStandardCoverLiteral.lean",
     "KltDP.Literature.Stacks.smooth_standardSmooth_cover_literal"),
    ("KltDP/Literature/SteinFactorizationNoetherian.lean",
     "KltDP.Literature.Stacks.steinFactorization_noetherian_literal"),
    ("KltDP/Literature/Tanaka/ContractionTheorem.lean",
     "KltDP.Literature.Tanaka.contraction_44_instance"),
    ("KltDP/Literature/ZariskiNormalCompletion.lean",
     "KltDP.Literature.Zariski.closedPoint_normal_completion_literal"),
)
LITERATURE_FILE_INDEX = dict(LITERATURE_AXIOM_FILES)
LITERATURE_NAMES = [name for _, name in LITERATURE_AXIOM_FILES]


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def discharge_literature_axiom(path: str, findings: list[dict]) -> tuple[list[dict], list[dict]]:
    """Discharge exactly one `axiom` rejection in an allowlisted literature file.

    Every other finding in that file and every finding in any other file is retained.
    An allowlisted file with zero or several axiom tokens is an error, never a pass.
    """
    if path not in LITERATURE_FILE_INDEX:
        return list(findings), []
    axiom_rows = [row for row in findings
                  if row.get("token") == "axiom" and row.get("severity") == "reject"]
    if len(axiom_rows) != 1:
        raise ValueError(f"Literature file must contain exactly one axiom token: {path} has {len(axiom_rows)}")
    target = axiom_rows[0]
    return [row for row in findings if row is not target], [dict(target)]


def load_literature_registry(root: Path):
    """Optional exact registry cross-check; its absence admits nothing beyond the file allowlist.

    Production acceptance additionally requires the registry bound in both build manifests
    by the compiled-audit parser. Returns (sha256, entries) or None.
    """
    registry = root / LITERATURE_REGISTRY
    if not registry.exists():
        return None
    raw = registry.read_bytes()
    record = json.loads(raw.decode("utf-8"), object_pairs_hook=unique_object)
    if not isinstance(record, dict) or record.get("schema") != LITERATURE_REGISTRY_SCHEMA or \
            record.get("policy") != SOURCE_POLICY_PROFILE:
        raise ValueError("Literature registry schema or policy profile differs from this source gate")
    entries = record.get("active_literature_axioms")
    if not isinstance(entries, list) or [(e.get("source_path"), e.get("name")) for e in entries] != \
            list(LITERATURE_AXIOM_FILES):
        raise ValueError("Literature registry entries differ from the exact twenty-eight-file allowlist")
    return hashlib.sha256(raw).hexdigest(), entries


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, help="write JSON source-lint report")
    parser.add_argument("--write-driver", type=Path,
                        help="write a Lean environment-audit driver; does not run Lean")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        print("Source-lexer regression checks passed; no Lean compilation performed.")
        return 0
    root = args.root.resolve()
    files = sorted(file for file in (root / "KltDP").rglob("*.lean")
                   if not any(part.startswith("._") for part in file.relative_to(root).parts))
    if (root / "KltDP.lean").exists():
        files.append(root / "KltDP.lean")
    if not files:
        parser.error(f"no Lean source files below {root}")
    registry = load_literature_registry(root)
    registry_sha256 = None if registry is None else registry[0]
    rows = []
    remaining_by_path = {}
    admitted_findings = []
    import_rows, import_rejections = [], []
    scanned = {file.relative_to(root).as_posix() for file in files}
    for file in files:
        relative = file.relative_to(root)
        source = file.read_text()
        tooling = is_audit_tooling(relative)
        imports, problems = inspect_imports(root, relative, source, scanned)
        import_rows.extend(imports)
        if not tooling:
            import_rejections.extend(problems)
        raw_findings = findings(source)
        remaining_by_path[relative.as_posix()] = raw_findings
        if not tooling:
            remaining, discharged = discharge_literature_axiom(relative.as_posix(), raw_findings)
            remaining_by_path[relative.as_posix()] = remaining
            admitted_findings.extend({
                "file": relative.as_posix(), "name": LITERATURE_FILE_INDEX[relative.as_posix()],
                "registry_sha256": registry_sha256, "finding": item,
            } for item in discharged)
        rows.append({
            "path": relative.as_posix(),
            "sha256": hashlib.sha256(file.read_bytes()).hexdigest(),
            "scope": "audit_tooling" if tooling else "mathematical_source",
            "findings": raw_findings,
        })
    file_hashes = {row["path"]: row["sha256"] for row in rows}
    if len(admitted_findings) != len({row["file"] for row in admitted_findings}):
        raise ValueError("An approved axiom token was discharged twice for one file")
    if registry is not None:
        for entry in registry[1]:
            actual = file_hashes.get(entry["source_path"])
            if actual != entry.get("source_sha256"):
                raise ValueError("Literature registry source hash differs from the scanned file: " + entry["source_path"])
        if len(admitted_findings) != len(LITERATURE_AXIOM_FILES):
            raise ValueError("The registry requires every one of the twenty-eight literature files to be present")
    rejected = [dict(file=row["path"], **finding)
                for row in rows if row["scope"] == "mathematical_source"
                for finding in remaining_by_path[row["path"]] if finding["severity"] == "reject"]
    reviews = [dict(file=row["path"], **finding)
               for row in rows if row["scope"] == "mathematical_source"
               for finding in remaining_by_path[row["path"]] if finding["severity"] == "review"]
    report = {
        "schema": "klt-source-lint-v1",
        "status": source_policy_status(rejected + import_rejections, reviews),
        "source_policy_profile": SOURCE_POLICY_PROFILE,
        "linter_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "proof_status": "not_assessed_by_source_lint",
        "literature_axiom_allowlist": LITERATURE_NAMES,
        "literature_admission": {
            "registry_path": LITERATURE_REGISTRY,
            "registry_sha256": registry_sha256,
            "files": [{"path": path, "name": name, "sha256": file_hashes.get(path)}
                      for path, name in LITERATURE_AXIOM_FILES],
        },
        "admitted_literature_findings": admitted_findings,
        "lexical_policy": {
            "rejected_leaf_names": sorted(REJECT),
            "rejected_leaf_prefixes": sorted(REJECT_PREFIXES),
            "tooling_exemption": "KltDP/Audit/Trust.lean",
            "reviewed_attribute_commands": list(REVIEWED_ATTRIBUTE_COMMANDS),
            "reviewed_attribute_followers": sorted(REVIEWED_ATTRIBUTE_FOLLOWERS),
            "reviewed_declaration_attributes": sorted(REVIEWED_DECLARATION_ATTRIBUTES),
            "review_findings_block_admission": True,
        },
        "mathematical_source_rejections": rejected,
        "mathematical_source_reviews": reviews,
        "imports": import_rows,
        "import_policy_rejections": import_rejections,
        "files": rows,
        "limitations": [
            "Lexical checks do not establish elaboration, kernel checking, theorem coverage or nonvacuity.",
            "Macro expansion, quoted identifiers, interpolated strings and imported constants need the compiled audit.",
            "Qualified ASCII identifiers are checked by leaf spelling, not Lean name resolution; aliases and dynamically constructed names can evade this lexer.",
            "ofReduce* rejection is conservative prefix policy and can flag an unrelated user identifier with that spelling.",
            "Rejecting debug.skipKernelTC and addDeclWithoutChecking spellings does not prove imported artifacts were kernel checked.",
            "Audit tooling is inventoried separately and cannot establish a mathematical result.",
            "Range-less unsafe environment entries are nonlogical data, not authenticated compiler output; exact-source rejection/review and pinned imports remain required.",
            "The two admitted attribute commands only enable the pinned graded-algebra instance or exact Types instance pair locally; changed targets, scope, priority and unknown continuation forms require review. This spelling gate does not authenticate name resolution.",
            "A clean remote build, compiled dependency report and semantic review are required.",
        ],
    }
    encoded = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    else:
        sys.stdout.write(encoded)
    if args.write_driver:
        args.write_driver.parent.mkdir(parents=True, exist_ok=True)
        args.write_driver.write_text(
            "import KltDP\nimport KltDP.Audit.Trust\n"
            "set_option maxRecDepth 100000\n"
            "set_option maxHeartbeats 0\n"
            "#klt_trust_report\n")
    return 0 if report["status"] == "source_lint_passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
