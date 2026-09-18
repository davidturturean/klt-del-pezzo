import KltDP.Geometry.ContractionPicardSplitting
import KltDP.Geometry.BirationalNumericalPullback
import KltDP.Geometry.RationalHodgeIndex
import KltDP.Geometry.SurfaceNumericalFinitenessProved
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The original numerical Picard rank under a minus-one contraction

The original Picard splitting supplies all integral classes. Their positive
integral multiples span the actual numerical quotient. Exceptional degree
minus one and injectivity of original numerical pullback then give a linear
equivalence with the target numerical quotient plus one rational coordinate.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsContraction

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {E : S.PrimeCurve} (hb : IsContraction S T b E)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (hminus : IsMinusOneCurve hS E)

/-- Original numerical pullback, with properness and birationality obtained
from the actual contraction. -/
def numericalPullback : T.NumericalClassGroup →ₗ[ℚ] S.NumericalClassGroup :=
  letI : IsProper b := hb.isProper
  BirationalNumericalPullback.pullback b hb.over_base
    ((isBirational_iff_isBirationalScheme b).mp hb.birational)

theorem numericalPullback_injective : Function.Injective hb.numericalPullback := by
  letI : IsProper b := hb.isProper
  exact BirationalNumericalPullback.pullback_injective b hb.over_base
    ((isBirational_iff_isBirationalScheme b).mp hb.birational)

theorem numericalPullback_picard (p : Additive T.toScheme.Pic) :
    hb.numericalPullback (T.picardNumericalMap p) =
      S.picardNumericalMap ((schemePicardPullbackHom b).toAdditive p) := rfl

theorem degree_numericalPullback (x : T.NumericalClassGroup) :
    S.numericalRestrictionDegree E (hb.numericalPullback x) = 0 := by
  letI : IsProper b := hb.isProper
  obtain ⟨z, _, himage, _, _⟩ := hb.center
  exact BirationalNumericalPullback.degree_pullback_exceptional b hb.over_base
    ((isBirational_iff_isBirationalScheme b).mp hb.birational) E ⟨z, himage⟩ x

/-- The actual exceptional Cartier class is the second coordinate. -/
def numericalDecompositionInv : (T.NumericalClassGroup × ℚ) →ₗ[ℚ] S.NumericalClassGroup where
  toFun x := hb.numericalPullback x.1 + x.2 •
    S.picardNumericalMap (cartierPicardHom S.toScheme (S.primeCurveCartier hS E))
  map_add' x y := by
    change hb.numericalPullback (x.1 + y.1) + (x.2 + y.2) • _ = _
    rw [map_add, add_smul]
    abel
  map_smul' a x := by
    change hb.numericalPullback (a • x.1) + (a * x.2) • _ = a • (_ + _)
    rw [map_smul, smul_add, smul_smul]

theorem numericalDecompositionInv_integral (a : T.toScheme.Pic) (n : ℤ) :
    hb.numericalDecompositionInv hS (T.picardNumericalMap (Additive.ofMul a), (n : ℚ)) =
      S.picardNumericalMap (Additive.ofMul
        ((hb.picardDecomposition hS hminus).symm (a, Multiplicative.ofAdd n))) := by
  rw [hb.picardDecomposition_symm_apply hS hminus]
  change hb.numericalPullback (T.picardNumericalMap (Additive.ofMul a)) +
      (n : ℚ) • S.picardNumericalMap
        (cartierPicardHom S.toScheme (S.primeCurveCartier hS E)) =
    S.picardNumericalMap ((schemePicardPullbackHom b).toAdditive (Additive.ofMul a) +
      n • cartierPicardHom S.toScheme (S.primeCurveCartier hS E))
  rw [numericalPullback_picard, map_add, map_zsmul, Int.cast_smul_eq_zsmul]

include hminus in
theorem degree_numericalDecompositionInv (x : T.NumericalClassGroup × ℚ) :
    S.numericalRestrictionDegree E (hb.numericalDecompositionInv hS x) = -x.2 := by
  have hE : E.picardRestrictionDegree
      (cartierPicardClass S.toScheme (S.primeCurveCartier hS E)) = -1 := by
    rw [← E.intersectionNumber_eq_picardRestrictionDegree]
    exact hminus.selfIntersection
  change S.numericalRestrictionDegree E (hb.numericalPullback x.1 + x.2 • _) = _
  rw [map_add, map_smul, degree_numericalPullback,
    S.numericalRestrictionDegree_picardNumericalMap]
  change 0 + x.2 * (E.picardRestrictionDegree
    (cartierPicardClass S.toScheme (S.primeCurveCartier hS E)) : ℚ) = -x.2
  rw [hE]
  ring

include hminus in
theorem numericalDecompositionInv_bijective :
    Function.Bijective (hb.numericalDecompositionInv hS) := by
  constructor
  · intro x y h
    have hn : x.2 = y.2 := by
      have hd := congrArg (S.numericalRestrictionDegree E) h
      rw [degree_numericalDecompositionInv hb hS hminus,
        degree_numericalDecompositionInv hb hS hminus] at hd
      exact neg_injective hd
    apply Prod.ext
    · apply hb.numericalPullback_injective
      change hb.numericalPullback x.1 + x.2 • _ =
        hb.numericalPullback y.1 + y.2 • _ at h
      rw [hn] at h
      exact add_right_cancel h
    · exact hn
  · intro c
    obtain ⟨n, hn, p, hp⟩ := S.numericalClass_exists_positive_integral_multiple c
    let a := hb.picardDecomposition hS hminus p.toMul
    have hclass : hb.numericalDecompositionInv hS
        (T.picardNumericalMap (Additive.ofMul a.1), (a.2.toAdd : ℚ)) = (n : ℚ) • c := by
      rw [numericalDecompositionInv_integral hb hS hminus]
      change S.picardNumericalMap (Additive.ofMul
        ((hb.picardDecomposition hS hminus).symm
          (hb.picardDecomposition hS hminus p.toMul))) = _
      rw [MulEquiv.symm_apply_apply]
      exact hp
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    refine ⟨(n : ℚ)⁻¹ • (T.picardNumericalMap (Additive.ofMul a.1), (a.2.toAdd : ℚ)), ?_⟩
    rw [map_smul, hclass, smul_smul, inv_mul_cancel₀ hnq, one_smul]

def numericalDecomposition : (T.NumericalClassGroup × ℚ) ≃ₗ[ℚ] S.NumericalClassGroup :=
  LinearEquiv.ofBijective (hb.numericalDecompositionInv hS)
    (hb.numericalDecompositionInv_bijective hS hminus)

include hb hS hminus in
/-- The original Picard number drops by exactly one under the actual
contraction of the supplied actual minus-one curve. -/
theorem picardRank_eq_add_one : S.picardRank = T.picardRank + 1 := by
  letI : FiniteDimensional ℚ T.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite T hb.regular
  change Module.finrank ℚ S.NumericalClassGroup = Module.finrank ℚ T.NumericalClassGroup + 1
  rw [← (hb.numericalDecomposition hS hminus).finrank_eq, Module.finrank_prod]
  simp only [Module.finrank_self]

end KltDP.Geometry.IsContraction

#check @KltDP.Geometry.IsContraction.picardRank_eq_add_one
#print axioms KltDP.Geometry.IsContraction.picardRank_eq_add_one
