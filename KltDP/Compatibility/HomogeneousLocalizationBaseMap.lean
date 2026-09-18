/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser

The map and quotient proofs below reuse the proved construction in pinned
Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean, lines 600-632,
revision c44e0c8ee63ca166450922a373c7409c5d26b00b. The sole mathematical
generalization allows the two original gradings to use different coefficient
rings. No scalar transport is applied to either actual localization type.
KltDP adaptations: 2026.
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section
namespace KltDP.HomogeneousLocalizationBaseMap
open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

variable {R S A B ι : Type*} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
  [AddCommMonoid ι] [DecidableEq ι]
  (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule S B)
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {P : Submonoid A} {Q : Submonoid B}

/-- The original numerator/denominator map between actual homogeneous
localizations, allowing different original scalar rings for their gradings. -/
def map (g : A →+* B)
    (comap_le : P ≤ Q.comap g) (hg : ∀ i, ∀ a ∈ 𝒜 i, g a ∈ ℬ i) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := Quotient.map'
    (fun x ↦ ⟨x.1, ⟨_, hg _ _ x.2.2⟩, ⟨_, hg _ _ x.3.2⟩, comap_le x.4⟩)
    fun x y (e : x.embedding = y.embedding) ↦ by
      apply_fun IsLocalization.map (Localization Q) g comap_le at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e
  map_add' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_add, Quotient.map'_mk'', num_add, map_add, map_mul, den_add]; rfl
  map_mul' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_mul, Quotient.map'_mk'', num_mul, map_mul, den_mul]; rfl
  map_zero' := by simp only [← mk_zero (𝒜 := 𝒜), Quotient.map'_mk'', deg_zero,
    num_zero, ZeroMemClass.coe_zero, map_zero, den_zero, map_one]; rfl
  map_one' := by simp only [← mk_one (𝒜 := 𝒜), Quotient.map'_mk'', deg_zero,
    num_one, ZeroMemClass.coe_zero, map_zero, den_one, map_one]; rfl

@[simp] theorem map_mk (g : A →+* B)
    (comap_le : P ≤ Q.comap g) (hg : ∀ i, ∀ a ∈ 𝒜 i, g a ∈ ℬ i)
    (x : NumDenSameDeg 𝒜 P) :
    map 𝒜 ℬ g comap_le hg (HomogeneousLocalization.mk x) =
      HomogeneousLocalization.mk ⟨x.1, ⟨_, hg _ _ x.2.2⟩, ⟨_, hg _ _ x.3.2⟩, comap_le x.4⟩ := rfl

end KltDP.HomogeneousLocalizationBaseMap

#print axioms KltDP.HomogeneousLocalizationBaseMap.map
