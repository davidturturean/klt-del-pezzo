/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveCoefficientCharts
import KltDP.Compatibility.GradedProjIso

/-! # Original fraction naturality for coefficient change and graded coordinates -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ) (φ : R →+* S)
  (eR : homogeneousRing R n ≃+* homogeneousRing R n)
  (heR : KltDP.GradedProjIso.PreservesDegrees (𝒜 := grading R n) (ℬ := grading R n) eR)
  (eS : homogeneousRing S n ≃+* homogeneousRing S n)
  (heS : KltDP.GradedProjIso.PreservesDegrees (𝒜 := grading S n) (ℬ := grading S n) eS)
  (hcompat : ∀ p, MvPolynomial.map φ (eR p) = eS (MvPolynomial.map φ p))

/-- A commuting square of the original polynomial maps induces the same
commuting square on their actual homogeneous fraction rings. -/
theorem coefficientMap_gradedAwayMap (a : homogeneousRing R n) (b : homogeneousRing S n)
    (hab : MvPolynomial.map φ a = b) :
    (coefficientMap n φ (eR a) (eS b) (by rw [hcompat, hab])).comp
        (KltDP.GradedProjIso.awayMap eR heR a (eR a) rfl) =
      (KltDP.GradedProjIso.awayMap eS heS b (eS b) rfl).comp
        (coefficientMap n φ a b hab) := by
  apply RingHom.ext
  intro z
  obtain ⟨q, rfl⟩ := HomogeneousLocalization.mk_surjective z
  apply HomogeneousLocalization.val_injective
  change Localization.mk (MvPolynomial.map φ (eR (q.num : homogeneousRing R n)))
      ⟨MvPolynomial.map φ (eR (q.den : homogeneousRing R n)), _⟩ =
    Localization.mk (eS (MvPolynomial.map φ (q.num : homogeneousRing R n)))
      ⟨eS (MvPolynomial.map φ (q.den : homogeneousRing R n)), _⟩
  refine congrArg₂ Localization.mk (hcompat q.num) ?_
  apply Subtype.ext
  exact hcompat q.den

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMap_gradedAwayMap
