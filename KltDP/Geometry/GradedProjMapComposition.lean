/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.GradedProjIso

/-! # Composition of the original graded-ring-equivalence Proj maps -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u v
namespace KltDP.GradedProjIso

variable {R : Type v} {A B C : Type u}
  [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B} {𝒞 : ℕ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  (e : A ≃+* B) (he : PreservesDegrees (𝒜 := 𝒜) (ℬ := ℬ) e)
  (f : B ≃+* C) (hf : PreservesDegrees (𝒜 := ℬ) (ℬ := 𝒞) f)

include he hf in
/-- The original composite ring equivalence preserves its actual grading. -/
theorem preservesDegrees_trans :
    PreservesDegrees (𝒜 := 𝒜) (ℬ := 𝒞) (e.trans f) :=
  fun n a => (he n a).trans (hf n (e a))

/-- Original homogeneous fraction maps compose without changing the chart rings. -/
theorem awayMap_comp (a : A) (b : B) (c : C) (hab : e a = b) (hbc : f b = c) :
    (awayMap f hf b c hbc).comp (awayMap e he a b hab) =
      awayMap (e.trans f) (preservesDegrees_trans e he f hf) a c
        (by change f (e a) = c; rw [hab, hbc]) := by
  subst b
  subst c
  apply RingHom.ext
  intro z
  obtain ⟨q, rfl⟩ := HomogeneousLocalization.mk_surjective z
  apply HomogeneousLocalization.val_injective
  rfl

/-- Contravariant composition of the actual scheme maps, proved on the
native full homogeneous affine cover. -/
theorem map_comp :
    map f hf ≫ map e he = map (e.trans f) (preservesDegrees_trans e he f hf) := by
  refine (Proj.affineOpenCover 𝒞).openCover.hom_ext _ _ fun s => ?_
  let a : A := e.symm (f.symm s.2)
  let b : B := f.symm s.2
  have ha : a ∈ 𝒜 s.1 :=
    (preservesDegrees_symm e he s.1 b).mp
      ((preservesDegrees_symm f hf s.1 s.2).mp s.2.2)
  have hb : b ∈ ℬ s.1 := (preservesDegrees_symm f hf s.1 s.2).mp s.2.2
  have hab : e a = b := e.apply_symm_apply _
  have hbc : f b = s.2 := f.apply_symm_apply _
  change Proj.awayι 𝒞 (s.2 : C) s.2.2 s.1.2 ≫ (map f hf ≫ map e he) =
    Proj.awayι 𝒞 (s.2 : C) s.2.2 s.1.2 ≫
      map (e.trans f) (preservesDegrees_trans e he f hf)
  rw [← Category.assoc, awayι_comp_map f hf s.1.2 b hb s.2 hbc,
    Category.assoc, awayι_comp_map e he s.1.2 a ha b hab,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    awayMap_comp e he f hf a b s.2 hab hbc]
  exact (awayι_comp_map (e.trans f) (preservesDegrees_trans e he f hf)
    s.1.2 a ha s.2 (by change f (e a) = s.2; rw [hab, hbc])).symm

end KltDP.GradedProjIso

#print axioms KltDP.GradedProjIso.map_comp
