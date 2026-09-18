import KltDP.Manuscript.Datum.AnticanonicalDegrees
import KltDP.Manuscript.S02.Projection

/-!
# The threshold class `N_t = L + t K_S`: exceptional degrees and square

Manuscript `source/manuscript.tex`, Lemma 3.3 (`lem:nef-threshold`), the identities
`N · D_i = ℓ (b_i − 2)` and `N² = (1 − 2ℓ) v + ℓ² K_S²` (lines 800–823), proved for every
rational `t` in place of `ℓ`. Nefness of `N_ℓ` itself is `KltDP.Manuscript.S03.NefThreshold`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface Matrix

universe u

namespace KltDP.Manuscript.S03

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-- The threshold class `N_t = L + t K_S ∈ N¹(S)_ℚ`. -/
def thresholdClass (t : ℚ) : R.S.NumericalClassGroup := R.Lnum + t • R.Knum

/-- The numerical degree of the canonical class is the canonical degree. -/
theorem numericalRestrictionDegree_Knum (C : R.S.PrimeCurve) :
    R.S.numericalRestrictionDegree C R.Knum = (R.Kdeg C : ℚ) := by
  change R.S.numericalRestrictionDegree C (NefNullCurveNegativeSquare.cartierClass R.S R.KS) = _
  rw [← R.rationalWeilNumericalMap_rationalCartier R.KS,
    R.numericalRestrictionDegree_rationalWeilNumericalMap,
    RationalWeilIntersection.degreeLinearMap_rationalCartier]
  rfl

/-- `N_t · D_i = t (b_i − 2)`: exceptional curves are `L`-null and `K_S · D_i = b_i − 2`. -/
theorem thresholdClass_degree_exceptional (t : ℚ) (i : R.Vertices) :
    R.S.numericalRestrictionDegree i.val (thresholdClass R t) = t * (R.w i - 2) := by
  simp only [thresholdClass, map_add, map_smul, smul_eq_mul]
  rw [R.numericalRestrictionDegree_Lnum, R.Ldeg_exceptional, numericalRestrictionDegree_Knum,
    R.Kdeg_exceptional]
  simp only [ResolutionDatum.q]
  ring

/-- `N_t · C = L · C + t K_S · C` for every prime curve. -/
theorem thresholdClass_degree (t : ℚ) (C : R.S.PrimeCurve) :
    R.S.numericalRestrictionDegree C (thresholdClass R t) = R.Ldeg C + t * (R.Kdeg C : ℚ) := by
  simp only [thresholdClass, map_add, map_smul, smul_eq_mul]
  rw [R.numericalRestrictionDegree_Lnum, numericalRestrictionDegree_Knum]

/-- `N_t² = (1 − 2t) v + t² K_S²`. -/
theorem thresholdClass_square (t : ℚ) :
    R.S.numericalIntersectionBilinForm R.hreg (thresholdClass R t) (thresholdClass R t) =
      (1 - 2 * t) * R.Lsq + t ^ 2 * R.Ksq := by
  simp only [thresholdClass, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, smul_eq_mul]
  have hsymm : R.S.numericalIntersectionBilinForm R.hreg R.Lnum R.Knum =
      R.S.numericalIntersectionBilinForm R.hreg R.Knum R.Lnum :=
    (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq R.Lnum R.Knum
  rw [hsymm, R.Knum_pairing_Lnum]
  simp only [ResolutionDatum.Lsq, ResolutionDatum.Ksq]
  ring

end KltDP.Manuscript.S03
