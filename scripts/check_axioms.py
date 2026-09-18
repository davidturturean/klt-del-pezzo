#!/usr/bin/env python3
"""Check `#print axioms` output against the repository trust boundary.

The accepted boundary is the three standard Lean principles plus the
admitted literature statements declared in `KltDP/Literature/`. The report
must contain the dependency line of the main theorem.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPORT_RE = re.compile(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL)
MAIN_THEOREM = "KltDP.Manuscript.uniformSevenPointBound"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
LITERATURE = {
    "KltDP.Literature.Hartshorne.castelnuovo_contraction_literal",
    "KltDP.Literature.Hartshorne.hasContractionLifts_instance",
    "KltDP.Literature.Hartshorne.hurwitz_degreeTwo_projectiveLine_instance",
    "KltDP.Literature.Hartshorne.integral_numerical_group_free_finite_literal",
    "KltDP.Literature.Hartshorne.minimal_surface_classification_literal",
    "KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal",
    "KltDP.Literature.Hartshorne.point_blowup_structure_cohomology_literal",
    "KltDP.Literature.Hartshorne.ruled_surface_genus_literal",
    "KltDP.Literature.Hartshorne.ruled_surface_picard_literal",
    "KltDP.Literature.Hartshorne.surface_hodge_index_literal",
    "KltDP.Literature.Hartshorne.surface_nakai_moishezon_literal",
    "KltDP.Literature.Hartshorne.surface_riemannRoch_literal",
    "KltDP.Literature.Keel.semiampleness_completeSystem_literal",
    "KltDP.Literature.Stacks.affine_morphism_cohomology_literal",
    "KltDP.Literature.Stacks.blowupRegularPoint_literal",
    "KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal",
    "KltDP.Literature.Stacks.field_isJ2",
    "KltDP.Literature.Stacks.lipman_resolution_of_normal_completions_literal",
    "KltDP.Literature.Stacks.properCohomology_finite",
    "KltDP.Literature.Stacks.properFlat_fiberEuler_literal",
    "KltDP.Literature.Stacks.proper_curve_pullback_degree_literal",
    "KltDP.Literature.Stacks.proper_curve_tensor_degree_literal",
    "KltDP.Literature.Stacks.regularLocal_isUFD",
    "KltDP.Literature.Stacks.regular_smooth_loci_perfect_literal",
    "KltDP.Literature.Stacks.smooth_standardSmooth_cover_literal",
    "KltDP.Literature.Stacks.steinFactorization_noetherian_literal",
    "KltDP.Literature.Tanaka.contraction_44_instance",
    "KltDP.Literature.Zariski.closedPoint_normal_completion_literal",
}
ALLOWED = STANDARD | LITERATURE


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("report", type=Path)
    parser.add_argument("--declaration", default=MAIN_THEOREM,
                        help="declaration whose dependency line must be present")
    args = parser.parse_args()
    text = args.report.read_text(encoding="utf-8", errors="replace")
    if "sorryAx" in text:
        print("ERROR: axiom report contains sorryAx")
        return 1
    matches = REPORT_RE.findall(text)
    if not matches:
        print("ERROR: no '#print axioms' dependency report was found")
        return 1
    bad = False
    seen = set()
    for index, (name, payload) in enumerate(matches, start=1):
        seen.add(name)
        deps = {item.strip() for item in payload.replace("\n", " ").split(",") if item.strip()}
        extras = deps - ALLOWED
        print(f"Report {index} ({name}): {len(deps)} dependencies, "
              f"{len(deps & LITERATURE)} literature, {len(deps & STANDARD)} standard")
        if extras:
            bad = True
            print(f"ERROR: unexpected dependency or project axiom: {sorted(extras)}")
    if args.declaration not in seen:
        print(f"ERROR: no dependency report for {args.declaration}")
        return 1
    if bad:
        return 1
    print(f"OK: every printed dependency is one of the {len(STANDARD)} standard principles "
          f"or the {len(LITERATURE)} admitted literature statements.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
