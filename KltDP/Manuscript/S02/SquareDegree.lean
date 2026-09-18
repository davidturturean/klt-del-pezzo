import KltDP.Geometry.NullCurveIntersectionMatrix
import KltDP.Geometry.NullCurveNumericalSpan
import KltDP.Geometry.CompatibleRationalAdjunctionDegree
import KltDP.Geometry.Resolution
import KltDP.Geometry.RegularSurfaceSmoothLiteralUse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Manuscript Lemma 2.5: square and degree formulas

Source: `source/manuscript.tex`, lines 461–488, label `lem:square-degree`.

On a regular normal projective surface `T` with a finite family of prime curves
`G_i`, the negative intersection matrix `A = -(G_i · G_j)`, the canonical-degree
vector `q_i = K_T · G_i`, coefficients `λ` with `A λ = q`, and the numerical classes
`B = Σ λ_i G_i`, `H = -(K_T + B)` in `N¹(T)_ℚ`:

* `square_formula`: `H² = K_T² + λᵀ q`;
* `square_formula_inverse`: `H² = K_T² + qᵀ A⁻¹ q` when `A` is invertible;
* `degree_formula`: `H · C = -K_T · C - pᵀ λ` with `p_i = C · G_i`, for every prime curve `C`
  (the manuscript's `C ⊄ G` is only needed to interpret `p_i` as a count; the identity
  holds for every prime curve, so no such hypothesis is taken);
* `minusOne_degree_formula`: `H · C = 1 - pᵀ λ` for a `(-1)`-curve `C`, when `K_T` is a
  canonical divisor (an identification of `O(K_T)` with the exterior square of the
  relative differentials, exactly as in `ResolutionDatum.eKS`).

All objects are the actual union objects: `NullCurveIntersectionMatrix.intersectionMatrix`,
`DisjointNegativeCurvesRank.curveClass`, `NefNullCurveNegativeSquare.cartierClass`, and the
descended intersection form `numericalIntersectionBilinForm`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open scoped BigOperators
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.DisjointNegativeCurvesRank KltDP.Geometry.NefNullCurveNegativeSquare
open KltDP.Geometry.NullCurveNumericalSpan KltDP.Geometry.NullCurveIntersectionMatrix

universe u

namespace KltDP.Manuscript.S02

variable {k : Type u} [Field k] [IsAlgClosed k] (T : NormalProjectiveSurface k)
  (hreg : ∀ x : T.Point, RegularPoint T.toScheme x)
  {ι : Type*} [Fintype ι] (G : ι → T.PrimeCurve)
  (K : CartierDivisor T.toScheme) (lam : ι → ℚ)

/-! ### The objects of Lemma 2.5 -/

/-- The negative intersection matrix `A = -(G_i · G_j)` of the family `G`. -/
def negIntersectionMatrix : Matrix ι ι ℚ := -(intersectionMatrix T hreg G)

/-- The canonical-degree vector `q_i = K_T · G_i`. -/
def canonicalDegreeVector : ι → ℚ := fun i => ((G i).intersectionNumber K : ℚ)

/-- The numerical class `B = Σ_i λ_i G_i`. -/
def curveCombination : T.NumericalClassGroup := ∑ i, lam i • curveClass T hreg (G i)

/-- The numerical class `H = -(K_T + B)`. -/
def adjustedClass : T.NumericalClassGroup := -(cartierClass T K + curveCombination T hreg G lam)

/-! ### Degrees of the basic classes on a prime curve -/

include hreg in
/-- The numerical degree of a Cartier class on a prime curve is the original
intersection number. -/
theorem numericalRestrictionDegree_cartierClass (C : T.PrimeCurve) (D : CartierDivisor T.toScheme) :
    T.numericalRestrictionDegree C (cartierClass T D) = (C.intersectionNumber D : ℚ) := by
  rw [← pairing_curveClass T hreg, cartierClass_curveClass T hreg D C]

/-- The numerical degree of a prime-curve class on a prime curve is the original
intersection number with the constructed prime Cartier divisor. -/
theorem numericalRestrictionDegree_curveClass (C E : T.PrimeCurve) :
    T.numericalRestrictionDegree C (curveClass T hreg E) =
      (C.intersectionNumber (T.primeCurveCartier hreg E) : ℚ) := by
  rw [← pairing_curveClass T hreg, curveClass_pairing T hreg E C,
    T.intersectionPairing_primeCurve hreg]

/-! ### The two pairings entering the square formula -/

/-- `K_T · B = λᵀ q`. -/
theorem cartierClass_pairing_curveCombination :
    T.numericalIntersectionBilinForm hreg (cartierClass T K) (curveCombination T hreg G lam) =
      dotProduct lam (canonicalDegreeVector T G K) := by
  unfold curveCombination canonicalDegreeVector dotProduct
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.smul_right, cartierClass_curveClass T hreg K (G i)]

/-- `B² = -λᵀ A λ = -λᵀ q` under the relation `A λ = q`. -/
theorem curveCombination_square
    (hlam : negIntersectionMatrix T hreg G *ᵥ lam = canonicalDegreeVector T G K) :
    T.numericalIntersectionBilinForm hreg (curveCombination T hreg G lam)
        (curveCombination T hreg G lam) =
      -dotProduct lam (canonicalDegreeVector T G K) := by
  have hM : intersectionMatrix T hreg G *ᵥ lam = -(canonicalDegreeVector T G K) := by
    rw [← hlam, negIntersectionMatrix, Matrix.neg_mulVec, neg_neg]
  rw [curveCombination, ← quadraticForm_eq T hreg G lam, hM, dotProduct_neg]

/-! ### Manuscript Lemma 2.5 -/

/-- Manuscript (eq:H-square) in the form `H² = K_T² + λᵀ q` (lines 461–488). -/
theorem square_formula
    (hlam : negIntersectionMatrix T hreg G *ᵥ lam = canonicalDegreeVector T G K) :
    T.numericalIntersectionBilinForm hreg (adjustedClass T hreg G K lam)
        (adjustedClass T hreg G K lam) =
      T.numericalIntersectionBilinForm hreg (cartierClass T K) (cartierClass T K) +
        dotProduct lam (canonicalDegreeVector T G K) := by
  have hsymm := LinearMap.BilinForm.IsSymm.eq (T.numericalIntersectionBilinForm_isSymm hreg)
    (curveCombination T hreg G lam) (cartierClass T K)
  unfold adjustedClass
  rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
    hsymm, cartierClass_pairing_curveCombination T hreg G K lam,
    curveCombination_square T hreg G K lam hlam]
  ring

/-- Manuscript (eq:H-square) literally: `H² = K_T² + qᵀ A⁻¹ q` when `A` is invertible. -/
theorem square_formula_inverse [DecidableEq ι]
    (hlam : negIntersectionMatrix T hreg G *ᵥ lam = canonicalDegreeVector T G K)
    (hA : IsUnit (negIntersectionMatrix T hreg G).det) :
    T.numericalIntersectionBilinForm hreg (adjustedClass T hreg G K lam)
        (adjustedClass T hreg G K lam) =
      T.numericalIntersectionBilinForm hreg (cartierClass T K) (cartierClass T K) +
        dotProduct (canonicalDegreeVector T G K)
          ((negIntersectionMatrix T hreg G)⁻¹ *ᵥ canonicalDegreeVector T G K) := by
  have hinv : (negIntersectionMatrix T hreg G)⁻¹ *ᵥ canonicalDegreeVector T G K = lam := by
    rw [← hlam, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  rw [hinv, dotProduct_comm]
  exact square_formula T hreg G K lam hlam

/-- Manuscript (eq:H-degree): `H · C = -K_T · C - pᵀ λ` with `p_i = C · G_i`, for every
prime curve `C` (no `C ⊄ G` hypothesis is needed for the identity). -/
theorem degree_formula (C : T.PrimeCurve) :
    T.numericalRestrictionDegree C (adjustedClass T hreg G K lam) =
      -((C.intersectionNumber K : ℚ)) -
        dotProduct (fun i => ((C.intersectionNumber (T.primeCurveCartier hreg (G i)) : ℚ))) lam := by
  have hsum : ∀ i, T.numericalRestrictionDegree C (lam i • curveClass T hreg (G i)) =
      (C.intersectionNumber (T.primeCurveCartier hreg (G i)) : ℚ) * lam i := fun i => by
    rw [map_smul, smul_eq_mul, numericalRestrictionDegree_curveClass T hreg C (G i), mul_comm]
  unfold adjustedClass curveCombination
  rw [map_neg, map_add, map_sum, numericalRestrictionDegree_cartierClass T hreg C K]
  simp only [hsum, dotProduct]
  ring

/-- Manuscript (eq:minus-one-degree): `H · C = 1 - pᵀ λ` for a `(-1)`-curve `C`, when `K_T`
is a canonical divisor (`O(K_T) ≅ Ω²`, as for `ResolutionDatum.eKS`). -/
theorem minusOne_degree_formula
    (eK : cartierDivisorModule T.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior T.structureMorphism 2)
    [IsSmoothOfRelativeDimension 2 T.structureMorphism]
    (C : T.PrimeCurve) (hC : IsMinusOneCurve hreg C) :
    T.numericalRestrictionDegree C (adjustedClass T hreg G K lam) =
      1 - dotProduct (fun i => ((C.intersectionNumber (T.primeCurveCartier hreg (G i)) : ℚ))) lam := by
  obtain ⟨e, he⟩ := hC.isoProjectiveLine
  have hK : C.intersectionNumber K = -1 := by
    rw [CompatibleRationalAdjunctionDegree.canonical_intersection_eq T hreg K eK C e he,
      hC.selfIntersection]
    norm_num
  rw [degree_formula T hreg G K lam C, hK]
  push_cast
  ring

/-- The same, with the smoothness instance discharged from regularity of `T`
(`isSmoothOfRelativeDimension_two_of_regularPoints`). -/
theorem minusOne_degree_formula_of_regular
    (eK : cartierDivisorModule T.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior T.structureMorphism 2)
    (C : T.PrimeCurve) (hC : IsMinusOneCurve hreg C) :
    T.numericalRestrictionDegree C (adjustedClass T hreg G K lam) =
      1 - dotProduct (fun i => ((C.intersectionNumber (T.primeCurveCartier hreg (G i)) : ℚ))) lam := by
  haveI := T.isSmoothOfRelativeDimension_two_of_regularPoints hreg
  exact minusOne_degree_formula T hreg G K lam eK C hC

end KltDP.Manuscript.S02

#print axioms KltDP.Manuscript.S02.square_formula
#print axioms KltDP.Manuscript.S02.square_formula_inverse
#print axioms KltDP.Manuscript.S02.degree_formula
#print axioms KltDP.Manuscript.S02.minusOne_degree_formula
#print axioms KltDP.Manuscript.S02.minusOne_degree_formula_of_regular
