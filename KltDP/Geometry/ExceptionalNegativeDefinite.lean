import KltDP.Support.NegativeDefiniteCore
import KltDP.Geometry.IntersectionPairingSymmetry
import KltDP.Geometry.MinimalResolutionCount
import KltDP.Geometry.SmoothSurfaceDivisorPicard

/-!
# Negative definiteness of the exceptional intersection matrix (F06 consumer for Prop. 2.4)

What Proposition 2.4 consumes is not the Hodge index theorem but only: *the intersection matrix of
the exceptional curves of a resolution is negative definite*. This module states that against the
unconditional bilinear pairing of E6/E7, through the geometry-free core
`KltDP.Support.NegativeDefinite.negDefinite_of_semidefiniteOn_of_nondegenerateOn`.

Ingredients already available, and used here:
* the **unconditional symmetric pairing** `intersectionPairing`/`picardPairing` (E6, E7);
* **finiteness of the exceptional set**, lane E's `IsResolution.exceptionalCurves_finite` (0BAJ), so
  the family really is a finite matrix;
* the accepted **orthogonality to pullbacks**, `PrimeCurveInclusionLift.restrictionDegree_pullback_eq_zero`:
  an exceptional curve `C`, being contracted to a point, has `C · π^*L = 0` for every `L`. This is the
  classical source of the distinguished vector `h = π^*(ample)` with `h ⊥ E_i`.

**Why two named hypotheses and not one.** Orthogonality to a vector of non-negative square does *not*
by itself force negative definiteness on the orthogonal family: see the counterexample proved in
`KltDP/Support/NegativeDefiniteCore.lean` (identity form on `K²`, which is symmetric and
non-degenerate, `h = (1,0)`, family `{(0,1)}` — positive definite on the family). The missing input is
the signature condition, i.e. that the ambient form has at most one positive direction; that is
precisely the content of the index theorem, which the F06 plan deliberately avoids. Consequently the
geometric input splits into exactly two named `Prop`s, each named for what would discharge it:

* `ExceptionalPairingNegSemidefinite` — the pairing is `≤ 0` on the span of the exceptional classes.
  Discharged by the Hodge index theorem (F06) or, for a contracted *fibre*, by the Stacks 0C5X linear
  algebra with the fibre class in the kernel.
* `ExceptionalPairingNondegenerate` — no nonzero class in that span pairs to zero with the whole span.
  Discharged by Mumford's contraction criterion, or by unimodularity of `Pic(S)` together with
  Prop. 2.4's own statement that `A` is invertible.

`exceptionalPairing_negDefinite` is then the consumer: under both, every nonzero rational class
supported on the exceptional curves has negative square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Support.NegativeDefinite

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- The rational classes of the exceptional prime curves of `π`. -/
def exceptionalClasses : Set S.RationalPicard :=
  {v | ∃ C : S.PrimeCurve, IsExceptionalCurve π C ∧
    v = S.picardTensorInclusion
      (Additive.ofMul (cartierPicardClass S.toScheme (S.primeCurveCartier hregular C)))}

/-- **Named hypothesis**: the pairing is negative semi-definite on the exceptional span. Discharged
by the Hodge index theorem (F06), or by Stacks 0C5X for a contracted fibre. -/
def ExceptionalPairingNegSemidefinite (B : LinearMap.BilinForm ℚ S.RationalPicard) : Prop :=
  NegSemidefiniteOn B (exceptionalClasses π hregular)

/-- **Named hypothesis**: the pairing is non-degenerate on the exceptional span. Discharged by
Mumford's contraction criterion, or by invertibility of `A` in Prop. 2.4. -/
def ExceptionalPairingNondegenerate (B : LinearMap.BilinForm ℚ S.RationalPicard) : Prop :=
  NondegenerateOn B (exceptionalClasses π hregular)

/-- **The exceptional intersection matrix is negative definite**, from the geometry-free core. This
is what Proposition 2.4 consumes; the full index theorem is not needed. -/
theorem exceptionalPairing_negDefinite (B : LinearMap.BilinForm ℚ S.RationalPicard)
    (hsymm : B.IsSymm)
    (hsemi : ExceptionalPairingNegSemidefinite π hregular B)
    (hnd : ExceptionalPairingNondegenerate π hregular B)
    {v : S.RationalPicard} (hv : v ∈ Submodule.span ℚ (exceptionalClasses π hregular))
    (hv0 : v ≠ 0) : B v v < 0 :=
  negDefinite_of_semidefiniteOn_of_nondegenerateOn hsymm hsemi hnd hv hv0

end KltDP.Geometry.NormalProjectiveSurface
