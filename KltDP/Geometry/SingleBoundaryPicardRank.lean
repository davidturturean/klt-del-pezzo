import KltDP.Geometry.FactorialAffineDivisorEquation
import KltDP.Geometry.CartierPicardFiniteSupport
import KltDP.Geometry.CartierPicardComparison
import KltDP.Geometry.RationalHodgeIndex
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# One actual boundary prime generates the original numerical quotient

The original divisor is principalized on the factorial affine chart.
Its remaining support lies on the original boundary prime. Clearing an
actual numerical class's denominator then gives the rank bound.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Integral generation of the original Picard group bounds the rank of
its original rational numerical quotient. -/
theorem picardRank_le_one_of_picard_generator
    (c : Additive X.toScheme.Pic)
    (hgen : ∀ p : Additive X.toScheme.Pic, ∃ m : ℤ, m • c = p) :
    X.picardRank ≤ 1 := by
  have hsurj : Function.Surjective
      (LinearMap.toSpanSingleton ℚ X.NumericalClassGroup (X.picardNumericalMap c)) := by
    intro v
    obtain ⟨n, hn, p, hp⟩ := X.numericalClass_exists_positive_integral_multiple v
    obtain ⟨m, hm⟩ := hgen p
    have hmul : (m : ℚ) • X.picardNumericalMap c = (n : ℚ) • v := by
      rw [← hp, ← hm, map_zsmul]
      exact Int.cast_smul_eq_zsmul ℚ m (X.picardNumericalMap c)
    refine ⟨(n : ℚ)⁻¹ * (m : ℚ), ?_⟩
    change ((n : ℚ)⁻¹ * (m : ℚ)) • X.picardNumericalMap c = v
    rw [← smul_smul, hmul]
    exact inv_smul_smul₀ (by exact_mod_cast (ne_of_gt hn)) v
  have hle := LinearMap.finrank_range_le
    (LinearMap.toSpanSingleton ℚ X.NumericalClassGroup (X.picardNumericalMap c))
  rw [LinearMap.range_eq_top.mpr hsurj] at hle
  simpa only [picardRank, finrank_top, Module.finrank_self] using hle

variable [IsAlgClosed k]

/-- All original Picard classes are integral multiples of the actual
boundary prime of a nonempty factorial affine chart. -/
theorem picard_generated_by_single_affine_boundary
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    [Nonempty U] [UniqueFactorizationMonoid Γ(X.toScheme, U)]
    (B : X.PrimeCurve)
    (hboundary : ∀ C : X.PrimeCurve, C.genericPoint ∉ U → C = B)
    (p : Additive X.toScheme.Pic) :
    ∃ m : ℤ, m • cartierPicardHom X.toScheme (X.primeCurveCartier hregular B) = p := by
  let c := cartierPicardHom X.toScheme (X.primeCurveCartier hregular B)
  let g : ℤ →+ Additive X.toScheme.Pic :=
    { toFun := fun m => m • c
      map_zero' := zero_zsmul c
      map_add' := fun m n => add_zsmul c m n }
  obtain ⟨D, hD⟩ := cartierPicardHom_surjective X.toScheme p
  let f := X.affineRationalEquation hU (X.cartierToWeilHom D)
  let E := D - principalCartierDivisorHom X.toScheme (Additive.ofMul f)
  have hEclass : cartierPicardHom X.toScheme E = cartierPicardHom X.toScheme D := by
    simp only [E, map_sub, cartierPicardHom_principal, sub_zero]
  have hzero (C : X.PrimeCurve) (hC : C.genericPoint ∈ U) :
      X.cartierToWeilHom E C = 0 := by
    change X.cartierToWeilHom
      (D - principalCartierDivisorHom X.toScheme (Additive.ofMul f)) C = 0
    rw [map_sub, X.cartierToWeilHom_principal f]
    exact X.sub_principal_affineRationalEquation_apply hU (X.cartierToWeilHom D) C hC
  have hmem : cartierPicardHom X.toScheme E ∈ g.range := by
    apply X.cartierPicardHom_mem_of_support hregular E g.range
    intro C hC
    have hCB := hboundary C (fun h => hC (hzero C h))
    subst C
    exact ⟨1, by simp [g, c]⟩
  obtain ⟨m, hm⟩ := hmem
  exact ⟨m, hm.trans (hEclass.trans hD)⟩

/-- The geometric one-boundary-prime criterion bounds the original
numerical Picard rank, with no numerical or Picard-generation premise. -/
theorem picardRank_le_one_of_single_affine_boundary
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    [Nonempty U] [UniqueFactorizationMonoid Γ(X.toScheme, U)]
    (B : X.PrimeCurve)
    (hboundary : ∀ C : X.PrimeCurve, C.genericPoint ∉ U → C = B) :
    X.picardRank ≤ 1 :=
  X.picardRank_le_one_of_picard_generator
    (cartierPicardHom X.toScheme (X.primeCurveCartier hregular B))
    (X.picard_generated_by_single_affine_boundary hregular hU B hboundary)

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.picardRank_le_one_of_picard_generator
#check @KltDP.Geometry.NormalProjectiveSurface.picard_generated_by_single_affine_boundary
#check @KltDP.Geometry.NormalProjectiveSurface.picardRank_le_one_of_single_affine_boundary
#print axioms KltDP.Geometry.NormalProjectiveSurface.picardRank_le_one_of_picard_generator
#print axioms KltDP.Geometry.NormalProjectiveSurface.picard_generated_by_single_affine_boundary
#print axioms KltDP.Geometry.NormalProjectiveSurface.picardRank_le_one_of_single_affine_boundary
