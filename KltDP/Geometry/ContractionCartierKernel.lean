import KltDP.Geometry.ActualContractionMorphismDescent
import KltDP.Geometry.SchemePointBlowupSequenceRestriction
import KltDP.Geometry.PrimeCurveComplementPicardKernel
import KltDP.Geometry.BirationalRationalWeilSupport
import KltDP.Geometry.NormalCartierWeilInjective
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal

/-!
# The original Cartier kernel of a one-curve contraction

The actual center fiber and the original isomorphism on its complement
show that the supplied prime is the only contracted prime. Original Weil
pushforward therefore detects every other coefficient. Normal Cartier-Weil
injectivity recovers the literal signed Cartier divisor from this support.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.IsContraction

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {E : S.PrimeCurve} (hb : IsContraction S T b E)

include hb in
/-- The actual contraction contracts precisely its original exceptional prime. -/
theorem isExceptionalCurve_iff_eq (C : S.PrimeCurve) :
    IsExceptionalCurve b C ↔ C = E := by
  constructor
  · intro hC
    by_contra hne
    obtain ⟨z, hz, hfiber, hpoint⟩ := hb.centerFiber_eq_curve
    let U : T.toScheme.Opens := ⟨({z} : Set T.toScheme)ᶜ, hz.isOpen_compl⟩
    have hCE : C.genericPoint ∉ (E : Set S.toScheme) :=
      (PrimeCurveComplementKernel.genericPoint_mem_complementOpen_iff E C).mpr hne
    have hU : b.base C.genericPoint ∈ U := by
      change C.genericPoint ∉ b.base ⁻¹' ({z} : Set T.toScheme)
      rw [hfiber]
      exact hCE
    have hiso : IsIso (b ∣_ U) := hpoint.toSchemeIsAt.isIso_restrict U (by simp [U])
    exact (IsExceptionalCurve.subset_exceptionalLocus b hC C.genericPoint_mem)
      ⟨U, hU, hiso⟩
  · rintro rfl
    obtain ⟨z, _, himage, _, _⟩ := hb.center
    exact ⟨z, himage⟩

/-- The kernel of original Weil pushforward consists of actual integer
multiples of the original exceptional prime, at the Cartier level. -/
theorem cartier_eq_zsmul_exceptional
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (D : CartierDivisor S.toScheme)
    (hD :
      letI : IsProper b := hb.isProper
      BirationalWeilPushforward.pushforward b
        ((isBirational_iff_isBirationalScheme b).mp hb.birational)
        (S.cartierToWeilHom D) = 0) :
    D = S.cartierToWeilHom D E • S.primeCurveCartier hS E := by
  letI : IsProper b := hb.isProper
  let hbir := (isBirational_iff_isBirationalScheme b).mp hb.birational
  apply S.cartierToWeilHom_injective
  rw [map_zsmul, S.cartierToWeilHom_primeCurveCartier hS]
  ext C
  by_cases hCE : C = E
  · subst C
    simp
  · have hC : ¬ IsExceptionalCurve b C := fun hc => hCE ((hb.isExceptionalCurve_iff_eq C).mp hc)
    obtain ⟨A, hA⟩ :=
      BirationalWeilPushforward.exists_abovePrimeCurve_of_not_exceptional b hbir C hC
    have hzero : S.cartierToWeilHom D C = 0 := by
      rw [hA]
      exact congrArg (fun Z : T.WeilDivisor => Z A) hD
    simp only [Finsupp.smul_apply, Finsupp.single_eq_of_ne (Ne.symm hCE), smul_zero, hzero]

end KltDP.Geometry.IsContraction

#check @KltDP.Geometry.IsContraction.cartier_eq_zsmul_exceptional
#print axioms KltDP.Geometry.IsContraction.cartier_eq_zsmul_exceptional
