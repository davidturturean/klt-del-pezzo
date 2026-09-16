import KltDP.Geometry.ProjectiveLineCanonicalFrameUnit
import KltDP.Geometry.OpenRestrictionExtOne

/-!
# `deg K_{P¹} = 2g − 2`: the canonical degree formula for the projective line

The accepted `SmoothCurveCanonicalDegree` defines, for a scheme over a field, the genus
`g := dim_k H¹(C, O_C)`, the canonical degree `deg K_C := χ(Ω_C) − χ(O_C)` (the Euler degree, not an
exponent) and states the Riemann–Roch/duality identity as the predicate
`CurveCanonical.CanonicalDegreeFormula f : deg K_C = 2·g − 2`, **not** proved there in general.

This module proves it for `P¹`:

* **`canonicalDegree_eq_neg_two : deg K_{P¹} = −2`**, with no hypothesis, from the frame atlas of
  `Ω_{P¹}` (`ProjectiveLineCanonicalFrameUnit.canonicalDegree_projectiveLine`: the overlap transition
  unit of the frames `dt`, `ds` is `−T⁻²`, and `deg = exponent` on `P¹` by the accepted
  `ProjectiveLineDegreeExponent.degree_eq_exponent`);
* **`canonicalDegreeFormula_projectiveLine : CanonicalDegreeFormula (P¹ → Spec k)`**, with the
  affine-vanishing literal `KltDP.Literature.Stacks.AffineVanishingLiteral` (Stacks 01XB, a
  hypothesis, **not** admitted) as the only hypothesis. The literal enters only through
  `g(P¹) = 0` (`OpenRestrictionExtOne.genus_projectiveLine_eq_zero_of_affineVanishing`); the value
  `deg K_{P¹} = −2` is unconditional.

Nothing is admitted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ProjectiveLineComparison
open KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry.ProjectiveLineCanonicalFormula

variable (k : Type u) [Field k]

/-- **`deg K_{P¹} = −2`**, unconditionally. -/
theorem canonicalDegree_eq_neg_two :
    CurveCanonical.canonicalDegree (projectiveSpaceToSpec k 1) = -2 :=
  ProjectiveLineCanonicalFrameUnit.canonicalDegree_projectiveLine k

/-- **`deg K_{P¹} = 2·g(P¹) − 2`**, with the affine-vanishing literal as the only hypothesis. -/
theorem canonicalDegreeFormula_projectiveLine (hV : AffineVanishingLiteral.{u}) :
    CurveCanonical.CanonicalDegreeFormula (projectiveSpaceToSpec k 1) := by
  rw [CurveCanonical.canonicalDegreeFormula_iff, canonicalDegree_eq_neg_two,
    OpenRestrictionExtOne.genus_projectiveLine_eq_zero_of_affineVanishing k hV]
  norm_num

end KltDP.Geometry.ProjectiveLineCanonicalFormula
