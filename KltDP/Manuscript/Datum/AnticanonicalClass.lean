import KltDP.Manuscript.Datum.ResolutionDatum
import KltDP.Geometry.BirationalAmplePullbackPositiveSquare
import KltDP.Geometry.QCartierPullback
import KltDP.Geometry.NefNullCurveNegativeSquare

/-!
# The anticanonical pullback `L = π^*(-K_X)` of a resolution datum

`L` is represented by the rational Weil divisor `R.Lweil = -π^*K_X` on `S`
(`ResolutionDatum.Lweil`). This module records its degrees against prime curves:
zero on every exceptional curve, and the identity `L · C = -K_S · C - Σ λ_i (D_i · C)`
which is the manuscript's `K_S + Σ λ_i D_i = -L` evaluated on `C`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript.ResolutionDatum

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-- The `L`-degree `L · C` of a prime curve, as a rational number. -/
def Ldeg (C : R.S.PrimeCurve) : ℚ := RationalWeilIntersection.degreeLinearMap R.S R.hreg C R.Lweil

/-- The `K_S`-degree of a prime curve. -/
def Kdeg (C : R.S.PrimeCurve) : ℤ := C.intersectionNumber R.KS

/-- The discrepancy divisor evaluated on a prime curve: `Δ · C = K_S · C + L · C`. -/
theorem Kdeg_add_Ldeg (C : R.S.PrimeCurve) :
    (R.Kdeg C : ℚ) + R.Ldeg C = RationalWeilIntersection.degreeLinearMap R.S R.hreg C R.Δ := by
  rw [← R.KS_add_Lweil, map_add, RationalWeilIntersection.degreeLinearMap_rationalCartier]
  rfl

/-- The numerical class `[L] ∈ N¹(S)_ℚ` of the anticanonical pullback. -/
def Lnum : R.S.NumericalClassGroup := R.S.rationalWeilNumericalMap R.hreg R.Lweil

/-- The manuscript's `v = L² = K_X²`, computed in `N¹(S)_ℚ`. -/
def Lsq : ℚ := R.S.numericalIntersectionBilinForm R.hreg R.Lnum R.Lnum

/-- The numerical class of the canonical divisor `K_S`. -/
def Knum : R.S.NumericalClassGroup := NefNullCurveNegativeSquare.cartierClass R.S R.KS

/-- `K_S²` computed in `N¹(S)_ℚ`. -/
def Ksq : ℚ := R.S.numericalIntersectionBilinForm R.hreg R.Knum R.Knum

theorem Ksq_eq_intersectionPairing :
    R.Ksq = (R.S.intersectionPairing R.hreg R.KS R.KS : ℚ) :=
  NefNullCurveNegativeSquare.cartierClass_pairing R.S R.hreg R.KS R.KS

end KltDP.Manuscript.ResolutionDatum
