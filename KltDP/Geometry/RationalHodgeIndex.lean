import KltDP.Geometry.NumericalIntersectionPairing
import KltDP.Geometry.CartierPicardEndpointRational

/-!
# Hodge inequalities on the original rational numerical quotient

The existing positive-denominator lemma clears an arbitrary element of the
actual rationalized Picard group. Its image in the existing numerical quotient
therefore has a positive integral multiple represented by an original Picard
class. The original integer Hodge inequality then transports through the
already constructed rational intersection form.

The geometric Hodge input remains explicit. No finite-dimensionality premise,
new quotient, or identification with an integral numerical group is used.
-/

noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The original integral Picard inclusion spans its actual rationalization. -/
theorem rationalPicard_mem_span_integral (v : X.RationalPicard) :
    v ∈ Submodule.span ℚ (Set.range X.picardTensorInclusion) := by
  induction v using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a p =>
      have hp : X.picardTensorInclusion p ∈
          Submodule.span ℚ (Set.range X.picardTensorInclusion) :=
        Submodule.subset_span ⟨p, rfl⟩
      have ha : (a ⊗ₜ[ℤ] p) = a • X.picardTensorInclusion p := by
        change (a ⊗ₜ[ℤ] p) = a • ((1 : ℚ) ⊗ₜ[ℤ] p)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ha]
      exact Submodule.smul_mem _ a hp
  | add v w hv hw => exact Submodule.add_mem _ hv hw

/-- A positive integer clears any rational Picard class, with a witness in the
original integral Picard group. -/
theorem rationalPicard_exists_positive_integral_multiple (v : X.RationalPicard) :
    ∃ n : ℕ, 0 < n ∧ ∃ p : Additive X.toScheme.Pic,
      X.picardTensorInclusion p = (n : ℚ) • v := by
  obtain ⟨n, hn, p, hp⟩ :=
    (mem_ratSpan_range_iff X.picardTensorInclusion.toAddMonoidHom v).mp
      (X.rationalPicard_mem_span_integral v)
  exact ⟨n, hn, p, by simpa only [Nat.cast_smul_eq_nsmul ℚ] using hp⟩

/-- Denominator clearing descends along the existing numerical quotient map. -/
theorem numericalClass_exists_positive_integral_multiple (c : X.NumericalClassGroup) :
    ∃ n : ℕ, 0 < n ∧ ∃ p : Additive X.toScheme.Pic,
      X.picardNumericalMap p = (n : ℚ) • c := by
  obtain ⟨v, rfl⟩ := X.rationalPicardNumericalMap_surjective c
  obtain ⟨n, hn, p, hp⟩ := X.rationalPicard_exists_positive_integral_multiple v
  refine ⟨n, hn, p, ?_⟩
  change X.rationalPicardNumericalMap (X.picardTensorInclusion p) = _
  rw [hp, map_smul]

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Integral Hodge semidefiniteness holds for every rational numerical class
orthogonal to the same original polarization class. -/
theorem numericalIntersection_nonpos_of_integralHodge (h : X.toScheme.Pic)
    (hHI : X.HodgeIndexSemidefinite hregular h) (c : X.NumericalClassGroup)
    (hperp : X.numericalIntersectionBilinForm hregular (X.picardNumericalClass h) c = 0) :
    X.numericalIntersectionBilinForm hregular c c ≤ 0 := by
  classical
  obtain ⟨n, hn, p, hp⟩ := X.numericalClass_exists_positive_integral_multiple c
  have hnq : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  have hperpInt : picardPairing X hregular h p.toMul = 0 := by
    have hzero : X.numericalIntersectionBilinForm hregular
        (X.picardNumericalMap (Additive.ofMul h)) (X.picardNumericalMap p) = 0 := by
      change X.numericalIntersectionBilinForm hregular (X.picardNumericalClass h)
        (X.picardNumericalMap p) = 0
      rw [hp, map_smul, hperp, smul_zero]
    rw [X.numericalIntersectionBilinForm_picard hregular] at hzero
    simpa only [toMul_ofMul, intCast_eq_zero_iff] using hzero
  have hnonpos : (picardPairing X hregular p.toMul p.toMul : ℚ) ≤ 0 := by
    exact_mod_cast hHI p.toMul hperpInt
  rw [← X.numericalIntersectionBilinForm_picard hregular p p, hp,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at hnonpos
  by_contra hpositive
  have hc : 0 < X.numericalIntersectionBilinForm hregular c c := lt_of_not_ge hpositive
  exact (not_lt_of_ge hnonpos) (mul_pos hnq (mul_pos hnq hc))

/-- Nonzero classes in the original rational numerical quotient have strictly
negative square when orthogonal to an integral Hodge class of positive square. -/
theorem numericalIntersection_neg_of_integralHodge (h : X.toScheme.Pic)
    (hpos : 0 < picardPairing X hregular h h)
    (hHI : X.HodgeIndexSemidefinite hregular h) (c : X.NumericalClassGroup)
    (hperp : X.numericalIntersectionBilinForm hregular (X.picardNumericalClass h) c = 0)
    (hc : c ≠ 0) : X.numericalIntersectionBilinForm hregular c c < 0 := by
  classical
  obtain ⟨n, hn, p, hp⟩ := X.numericalClass_exists_positive_integral_multiple c
  have hnq : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  have hperpInt : picardPairing X hregular h p.toMul = 0 := by
    have hzero : X.numericalIntersectionBilinForm hregular
        (X.picardNumericalMap (Additive.ofMul h)) (X.picardNumericalMap p) = 0 := by
      change X.numericalIntersectionBilinForm hregular (X.picardNumericalClass h)
        (X.picardNumericalMap p) = 0
      rw [hp, map_smul, hperp, smul_zero]
    rw [X.numericalIntersectionBilinForm_picard hregular] at hzero
    simpa only [toMul_ofMul, intCast_eq_zero_iff] using hzero
  have hpnontrivial : ¬ X.NumericallyTrivial p.toMul := by
    intro htrivial
    have hzero := (X.picardNumericalMap_eq_zero_iff p).mpr htrivial
    rw [hp] at hzero
    exact hc ((smul_eq_zero.mp hzero).resolve_left (ne_of_gt hnq))
  have hnegative : (picardPairing X hregular p.toMul p.toMul : ℚ) < 0 := by
    exact_mod_cast X.picardPairing_neg_of_orthogonal hregular h hpos hHI
      p.toMul hperpInt hpnontrivial
  rw [← X.numericalIntersectionBilinForm_picard hregular p p, hp,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at hnegative
  by_contra hnonnegative
  have hcc : 0 ≤ X.numericalIntersectionBilinForm hregular c c :=
    le_of_not_gt hnonnegative
  exact (not_lt_of_ge (mul_nonneg hnq.le (mul_nonneg hnq.le hcc))) hnegative

/-- The same semidefinite inequality on the original rationalized Picard group. -/
theorem rationalPicardIntersection_nonpos_of_integralHodge (h : X.toScheme.Pic)
    (hHI : X.HodgeIndexSemidefinite hregular h) (v : X.RationalPicard)
    (hperp : X.rationalPicardIntersectionBilinForm hregular
      (X.picardTensorInclusion (Additive.ofMul h)) v = 0) :
    X.rationalPicardIntersectionBilinForm hregular v v ≤ 0 := by
  exact X.numericalIntersection_nonpos_of_integralHodge hregular h hHI
    (X.rationalPicardNumericalMap v) hperp

/-- The integral Hodge signature gives a positive direction and a negative
definite orthogonal complement in the existing rational numerical quotient. -/
theorem numericalHodgeIndex_of_signature (hsig : X.HodgeIndexSignature hregular) :
    ∃ h : X.NumericalClassGroup,
      0 < X.numericalIntersectionBilinForm hregular h h ∧
      ∀ c : X.NumericalClassGroup,
        X.numericalIntersectionBilinForm hregular h c = 0 → c ≠ 0 →
        X.numericalIntersectionBilinForm hregular c c < 0 := by
  obtain ⟨h, hpos, hHI⟩ := hsig
  refine ⟨X.picardNumericalClass h, ?_, fun c hperp hc =>
    X.numericalIntersection_neg_of_integralHodge hregular h hpos hHI c hperp hc⟩
  change 0 < X.numericalIntersectionBilinForm hregular
    (X.picardNumericalMap (Additive.ofMul h)) (X.picardNumericalMap (Additive.ofMul h))
  rw [X.numericalIntersectionBilinForm_picard hregular]
  exact_mod_cast hpos

end KltDP.Geometry.NormalProjectiveSurface
