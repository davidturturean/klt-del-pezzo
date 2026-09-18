import KltDP.Geometry.SquareZeroIndependentSections
import KltDP.Geometry.EffectiveWeilAmpleDegree
import KltDP.Geometry.SectionEffectiveWeil

/-! The original negative fiber line has vanishing H0 and H1.
Actual effective representatives give strict ample degree, and original
Cartier RR with negative-nef vanishing proves the cohomology statement.
This is the ideal-sequence input for connectedness of actual members. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)
  (hrational : Scheme.BirationalOver X.structureMorphism
    (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))

local instance negativeSectionsIntegral : IsIntegral X.toScheme := X.integral

include eK hrational in
/-- The original square-zero class has strictly positive ample degree. -/
theorem squareZero_ample_pairing_pos (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (A : CartierDivisor X.toScheme)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A)) :
    0 < X.intersectionPairing hX F A := by
  letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme F)
  obtain ⟨s, hs⟩ := X.exists_two_independent_sections_of_nef_squareZero
    hX K eK hrational F hF hFF hKF
  obtain ⟨D, hD, hDF⟩ := X.exists_effectiveWeil_of_nonzero_cartier_section F (s 0) (hs.ne_zero 0)
  let e := X.regularCartierWeilEquiv hX
  have hrep : e.symm (X.cartierToWeilHom F) = F := e.symm_apply_apply F
  have hDK : X.intersectionPairing hX (e.symm D) K = X.intersectionPairing hX F K := by
    rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent X hX K hDF, hrep]
  have hDne : D ≠ 0 := by
    intro hz
    rw [hz, map_zero, X.intersectionPairing_zero_left,
      X.intersectionPairing_symm hX F K, hKF] at hDK
    omega
  have hp := X.effectiveWeil_ample_pairing_pos hX D hD hDne A hA
  rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent X hX A hDF,
    hrep] at hp
  exact hp

include eK hrational in
/-- Both original H0 and H1 of O(-F) vanish, with the native base action. -/
theorem squareZero_negative_hZero_hOne_eq_zero (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme (-F)) 0 = 0 ∧
      cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme (-F)) 1 = 0 := by
  obtain ⟨A, hA, hAnef⟩ := X.exists_isAmple_isNef_cartier
  have hFA := X.squareZero_ample_pairing_pos hX K eK hrational F hF hFF hKF A hA
  have hneg : X.intersectionPairing hX (-F) A < 0 := by
    rw [X.intersectionPairing_neg_left]
    omega
  have hz : cohomologyDimension X.structureMorphism
      (cartierDivisorModule X.toScheme (-F)) 0 = 0 := by
    simpa only [one_smul] using NegativeNefCartierPowers.hZero_positive_multiple_eq_zero
      X hX (-F) A hAnef hneg 1 Nat.one_pos
  have hdualNeg : X.intersectionPairing hX (K + F) F < 0 := by
    rw [X.intersectionPairing_add_left, hKF, hFF]
    norm_num
  have hd : cohomologyDimension X.structureMorphism
      (cartierDivisorModule X.toScheme (K + F)) 0 = 0 := by
    simpa only [one_smul] using NegativeNefCartierPowers.hZero_positive_multiple_eq_zero
      X hX (K + F) F hF hdualNeg 1 Nat.one_pos
  have hp : X.intersectionPairing hX (-F) ((-F) - K) = -2 := by
    rw [X.intersectionPairing_neg_left, sub_eq_add_neg, X.intersectionPairing_add_right,
      X.intersectionPairing_neg_right, X.intersectionPairing_neg_right, hFF,
      X.intersectionPairing_symm hX F K, hKF]
    norm_num
  have hchi := (X.structureCohomology_of_rational hX hrational).1
  have hrr := X.cartier_riemannRoch hX K eK (-F)
  rw [sub_neg_eq_add, hz, hd, hp, hchi] at hrr
  norm_num at hrr
  exact ⟨hz, hrr⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_negative_hZero_hOne_eq_zero
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_negative_hZero_hOne_eq_zero
