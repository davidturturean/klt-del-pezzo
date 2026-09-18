import KltDP.Geometry.ReducedSupportCartier
import KltDP.Geometry.QCartierPullback
import Mathlib.Tactic.Linarith

/-!
# Reduced Cartier supports containing a weighted boundary

An effective Cartier correction cannot cancel the effective Cartier
divisor controlling the boundary support. The boundary itself may have
arbitrary signed rational coefficients.
-/

noncomputable section
open AlgebraicGeometry
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

theorem rational_boundary_add_support_subset
    (B : X.RationalWeilDivisor) (A E : CartierDivisor X.toScheme)
    (hA : EffectiveDivisor (X.cartierToWeilHom A))
    (hE : EffectiveDivisor (X.cartierToWeilHom E))
    (hB : B.support ⊆ (X.cartierToWeilHom A).support) :
    (X.rationalCartierToWeilHom E + B).support ⊆
      (X.cartierToWeilHom (A + E)).support := by
  classical
  intro C hC
  by_contra hnot
  have hsum : X.cartierToWeilHom A C + X.cartierToWeilHom E C = 0 := by
    simpa only [map_add, Finsupp.add_apply] using (Finsupp.not_mem_support_iff.mp hnot)
  have hAz : X.cartierToWeilHom A C = 0 := by linarith [hA C, hE C]
  have hEz : X.cartierToWeilHom E C = 0 := by linarith [hA C, hE C]
  have hBz : B C = 0 := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp (hB (Finsupp.mem_support_iff.mpr hne))) hAz
  apply (Finsupp.mem_support_iff.mp hC)
  change (X.cartierToWeilHom E C : ℚ) + B C = 0
  rw [hEz, hBz]
  norm_num

variable [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]

theorem reducedSupportCartier_finsupp_support (D : CartierDivisor X.toScheme) :
    (X.cartierToWeilHom (X.reducedSupportCartier D)).support =
      (X.cartierToWeilHom D).support := by
  classical
  ext C
  simp only [Finsupp.mem_support_iff, X.reducedSupportCartier_coefficient]
  split_ifs <;> simp_all

theorem reducedSupportCartier_coefficient_zero_or_one
    (D : CartierDivisor X.toScheme) (C : X.PrimeCurve) :
    X.cartierToWeilHom (X.reducedSupportCartier D) C = 0 ∨
      X.cartierToWeilHom (X.reducedSupportCartier D) C = 1 := by
  rw [X.reducedSupportCartier_coefficient]
  split_ifs <;> simp

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.rational_boundary_add_support_subset
#print axioms KltDP.Geometry.NormalProjectiveSurface.reducedSupportCartier_finsupp_support
