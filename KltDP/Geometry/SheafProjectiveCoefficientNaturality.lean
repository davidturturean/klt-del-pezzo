/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.GradedProjMapComposition
import KltDP.Geometry.ProjectiveCoefficientGradedNaturality
import KltDP.Geometry.SheafProjectiveFrameTransitions

/-! # Actual projective frame transitions commute with original restriction maps -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.RelativeSymmetricProj
open KltDP.SymmetricAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  {n : ℕ} (b c : Basis (Fin (n + 1)) R M)

/-- The existing transition through the intrinsic symmetric Proj is exactly
the Proj map of the original inverse change of polynomial coordinates. -/
theorem transition_hom_eq_gradedMap :
    (transition b c).hom = KltDP.GradedProjIso.map (coordinateChange c b).toRingEquiv
      (fun d p => (coordinateChange_mem_iff c b d p).symm) := by
  exact KltDP.GradedProjIso.map_comp
    (equivMvPolynomial c).toRingEquiv.symm
    (KltDP.GradedProjIso.preservesDegrees_symm (equivMvPolynomial c).toRingEquiv
      (fun d p => (equivMvPolynomial_mem_homogeneous_iff c d p).symm))
    (equivMvPolynomial b).toRingEquiv
    (fun d p => (equivMvPolynomial_mem_homogeneous_iff b d p).symm)

variable {S N : Type u} [CommRing S] [AddCommGroup N] [Module S N]
  {φ : R →+* S} (b' c' : Basis (Fin (n + 1)) S N)
  (f : M →ₛₗ[φ] N) (hb : ∀ i, f (b i) = b' i) (hc : ∀ i, f (c i) = c' i)

include f hb hc

/-- An original semilinear restriction preserving both actual pairs of
frames gives scheme-level naturality of their genuine projective transitions. -/
theorem transition_coefficientMorphism :
    (transition b' c').hom ≫ RelativeProjectiveChart.coefficientMorphism n φ =
      RelativeProjectiveChart.coefficientMorphism n φ ≫ (transition b c).hom := by
  rw [transition_hom_eq_gradedMap b' c', transition_hom_eq_gradedMap b c]
  apply RelativeProjectiveChart.coefficientMorphism_gradedMap
  intro p
  exact coordinateChange_map c b c' b' f hc hb p

end KltDP.Geometry.RelativeSymmetricProj

#print axioms KltDP.Geometry.RelativeSymmetricProj.transition_hom_eq_gradedMap
#print axioms KltDP.Geometry.RelativeSymmetricProj.transition_coefficientMorphism
