/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import KltDP.Compatibility.HomComplexSingleCochain

/-!
# Cocycles from a single complex and their coboundaries

Port of the from-single cocycle API at Mathlib
79d0395a1825a6264ad5d269e35e60537518955e, with the small pre/postcomposition
and coboundary definitions it needs. All cocycles and differentials are
those of the pinned Hom complex. Explicit projection and arithmetic proofs
replace newer generated attributes and tactics. No quotient or Ext
comparison is defined or assumed here.
-/

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex.HomComplex

variable {F G K : CochainComplex C ℤ}

/-- Precomposition with an actual morphism of cochain complexes. -/
def Cocycle.precomp {n : ℤ} (z : Cocycle G K n) (f : F ⟶ G) : Cocycle F K n :=
  Cocycle.mk ((Cochain.ofHom f).comp z (zero_add n)) _ rfl (by simp)

@[simp]
lemma Cocycle.precomp_coe {n : ℤ} (z : Cocycle G K n) (f : F ⟶ G) :
    (z.precomp f : Cochain F K n) =
      (Cochain.ofHom f).comp (z : Cochain G K n) (zero_add n) := rfl

/-- Postcomposition with an actual morphism of cochain complexes. -/
def Cocycle.postcomp {n : ℤ} (z : Cocycle F G n) (f : G ⟶ K) : Cocycle F K n :=
  Cocycle.mk (z.1.comp (Cochain.ofHom f) (add_zero n)) _ rfl (by simp)

@[simp]
lemma Cocycle.postcomp_coe {n : ℤ} (z : Cocycle F G n) (f : G ⟶ K) :
    (z.postcomp f : Cochain F K n) =
      (z : Cochain F G n).comp (Cochain.ofHom f) (add_zero n) := rfl

/-- The subgroup of actual cocycles that are differentials of cochains. -/
def coboundaries (K L : CochainComplex C ℤ) (n : ℤ) : AddSubgroup (Cocycle K L n) where
  carrier := setOf (fun α => ∃ (m : ℤ) (_ : m + 1 = n) (β : Cochain K L m), δ m n β = α)
  zero_mem' := ⟨n - 1, by simp, 0, by simp⟩
  add_mem' := by
    rintro α₁ α₂ ⟨m, hm, β₁, hβ₁⟩ ⟨m', hm', β₂, hβ₂⟩
    obtain rfl : m = m' := by omega
    exact ⟨m, hm, β₁ + β₂, by simp [hβ₁, hβ₂]⟩
  neg_mem' := by
    rintro α ⟨m, hm, β, hβ⟩
    exact ⟨m, hm, -β, by simp [hβ]⟩

lemma mem_coboundaries_iff {K L : CochainComplex C ℤ} {n : ℤ}
    (α : Cocycle K L n) (m : ℤ) (hm : m + 1 = n) :
    α ∈ coboundaries K L n ↔ ∃ (β : Cochain K L m), δ m n β = α := by
  change (∃ (m' : ℤ) (_ : m' + 1 = n) (β : Cochain K L m'), δ m' n β = α) ↔ _
  constructor
  · rintro ⟨m', hm', β, hβ⟩
    obtain rfl : m' = m := by omega
    exact ⟨β, hβ⟩
  · rintro ⟨β, hβ⟩
    exact ⟨m, hm, β, hβ⟩

variable [HasZeroObject C] {X : C}

namespace Cocycle

/-- Constructor for cocycles from a single complex. -/
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    Cocycle ((singleFunctor C p).obj X) K n :=
  Cocycle.mk (Cochain.fromSingleMk f h) _ rfl (by
    rw [Cochain.δ_fromSingleMk _ _ _ q' (by omega), hf]
    simp)

@[simp]
lemma fromSingleMk_coe {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    (fromSingleMk f h q' hq' hf : Cochain ((singleFunctor C p).obj X) K n) =
      Cochain.fromSingleMk f h := rfl

lemma fromSingleMk_precomp {X' : C} (g : X' ⟶ X) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (g ≫ f) h q' hq' (by simp [hf]) =
      (fromSingleMk f h q' hq' hf).precomp ((singleFunctor C p).map g) := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_precomp])

lemma fromSingleMk_postcomp {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) {L : CochainComplex C ℤ}
    (g : K ⟶ L) :
    fromSingleMk (f ≫ g.f q) h q' hq' (by simp [reassoc_of% hf]) =
      (fromSingleMk f h q' hq' hf).postcomp g := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_postcomp])

lemma fromSingleMk_surjective {p n : ℤ} (α : Cocycle ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) (q' : ℤ) (hq' : q + 1 = q') :
    ∃ (f : X ⟶ K.X q) (hf : f ≫ K.d q q' = 0), fromSingleMk f h q' hq' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective α.1 q h
  have hα := α.δ_eq_zero (n + 1)
  rw [← hf, Cochain.δ_fromSingleMk _ _ _ q' (by omega)] at hα
  replace hα := Cochain.congr_v hα p q' (by omega)
  refine ⟨f, ?_, ?_⟩
  · apply (cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom).1
    simpa only [Cochain.fromSingleMk_v, Cochain.zero_v, comp_zero] using hα
  · apply Cocycle.ext
    exact hf

lemma fromSingleMk_add {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f + g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf + fromSingleMk g h q' hq' hg := by
  apply Cocycle.ext
  simp only [fromSingleMk_coe, coe_add, Cochain.fromSingleMk_add]

lemma fromSingleMk_sub {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f - g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf - fromSingleMk g h q' hq' hg := by
  apply Cocycle.ext
  simp only [fromSingleMk_coe, coe_sub, Cochain.fromSingleMk_sub]

lemma fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (-f) h q' hq' (by simp [hf]) = - fromSingleMk f h q' hq' hf := by
  apply Cocycle.ext
  simp only [fromSingleMk_coe, coe_neg, Cochain.fromSingleMk_neg]

variable (X K) in
@[simp]
lemma fromSingleMk_zero {p q : ℤ} {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') :
    fromSingleMk (0 : X ⟶ K.X q) h q' hq' (by simp) = 0 := by
  apply Cocycle.ext
  simp only [fromSingleMk_coe, coe_zero, Cochain.fromSingleMk_zero]

lemma fromSingleMk_mem_coboundaries_iff {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0)
    (q'' : ℤ) (hq'' : q'' + 1 = q) :
    fromSingleMk f h q' hq' hf ∈ coboundaries _ _ _ ↔
      ∃ (g : X ⟶ K.X q''), g ≫ K.d q'' q = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.fromSingleMk_surjective α q'' (by omega)
    refine ⟨g, ?_⟩
    rw [← hg, fromSingleMk_coe, Cochain.δ_fromSingleMk _ _ _ _ h] at hα
    exact (Cochain.fromSingleEquiv h).symm.injective hα
  · rintro ⟨g, rfl⟩
    exact ⟨Cochain.fromSingleMk g (by omega), Cochain.δ_fromSingleMk _ _ _ _ h⟩


end Cocycle

end CochainComplex.HomComplex
