/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import KltDP.Compatibility.HomComplexShiftCocycle
import KltDP.Compatibility.HomComplexCohomologyNaturality

/-!
# Cohomology classes as actual morphisms in the homotopy category

Port of the quotient-to-homotopy-category block of official Mathlib
`HomComplexCohomology` at 79d0395a1825a6264ad5d269e35e60537518955e.
The pinned quotient's homotopy API supplies its zero criterion. The map
is proved well-defined by an explicit signed homotopy, then injective
and surjective. Its postcomposition equation uses the actual shifted
coefficient morphism. No derived localization or Ext comparison is
assumed or constructed in this file.
-/

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace HomotopyCategory

/-- A cochain map is zero in the original homotopy quotient exactly when
it is homotopic to zero. -/
lemma quotient_map_eq_zero_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (quotient C (.up ℤ)).map f = 0 ↔ Nonempty (Homotopy f 0) := by
  constructor
  · intro h
    exact ⟨homotopyOfEq f 0 (by simpa using h)⟩
  · rintro ⟨h⟩
    simpa using eq_of_homotopy f 0 h

end HomotopyCategory

namespace CochainComplex.HomComplex.CohomologyClass

variable {K L M : CochainComplex C ℤ} {n : ℤ}

/-- Send an actual cohomology class to its corresponding morphism in the
original homotopy category. -/
noncomputable def toHom :
    CohomologyClass K L n →+
      ((HomotopyCategory.quotient C _).obj K ⟶
        (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
  descAddMonoidHom ((Functor.mapAddHom _).comp Cocycle.equivHomShift.symm.toAddMonoidHom) (by
    rintro ⟨x, hx⟩ ⟨m, hm, β, rfl⟩
    change (HomotopyCategory.quotient C _).map
      (Cocycle.equivHomShift.symm (⟨δ m n β, hx⟩ : Cocycle K L n)) = 0
    rw [Cocycle.equivHomShift_symm_apply, HomotopyCategory.quotient_map_eq_zero_iff]
    exact ⟨(Cochain.equivHomotopy _ _).symm ⟨n.negOnePow • β.rightShift _ _ (by omega),
      by simp [Cochain.δ_rightShift _ _ _ _ _ _ (zero_add n), smul_smul]⟩⟩)

lemma toHom_mk (x : Cocycle K L n) :
    toHom (mk x) =
      (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) := rfl

/-- The zero class criterion agrees with the actual homotopy quotient's
zero morphism criterion. -/
lemma toHom_mk_eq_zero_iff (x : Cocycle K L n) :
    toHom (mk x) = 0 ↔ x ∈ coboundaries K L n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [coboundaries, exists_prop, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    rw [toHom_mk, HomotopyCategory.quotient_map_eq_zero_iff] at h
    obtain ⟨γ, h⟩ := Cochain.equivHomotopy _ _ h.some
    simp only [Cochain.ofHom_zero, add_zero, Cocycle.equivHomShift_symm_apply,
      Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.rightShift_coe] at h
    exact ⟨n - 1, by simp, n.negOnePow • γ.rightUnshift _ (by omega),
      by simp [Cochain.δ_rightUnshift _ _ _ _ _ (zero_add n), smul_smul, ← h]⟩
  · rw [← mk_eq_zero_iff] at h
    rw [h, map_zero]

variable (K L n) in
lemma toHom_bijective : Function.Bijective (toHom : CohomologyClass K L n → _) := by
  refine ⟨fun x y h ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero, ← mk_sub, mk_eq_zero_iff, ← toHom_mk_eq_zero_iff,
      mk_sub, map_sub, h, sub_self]
  · obtain ⟨f, rfl⟩ := Functor.map_surjective _ f
    exact ⟨mk (Cocycle.equivHomShift f), by simp [toHom_mk]⟩

/-- Actual cohomology classes identify with morphisms into the shifted
target in the original homotopy category. -/
noncomputable def homAddEquiv :
    CohomologyClass K L n ≃+
      ((HomotopyCategory.quotient C _).obj K ⟶
        (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
  AddEquiv.ofBijective toHom (toHom_bijective _ _ _)

@[simp]
lemma homAddEquiv_apply (x : CohomologyClass K L n) :
    homAddEquiv x = toHom x := rfl

/-- This comparison commutes with the actual postcomposition map and
the shift of the original coefficient morphism. -/
lemma toHom_postcomp (x : CohomologyClass K L n) (f : L ⟶ M) :
    toHom (KltDP.HomComplexComparison.cohomologyClassPostcomp f n x) =
      toHom x ≫ (HomotopyCategory.quotient C _).map (f⟦n⟧') := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [KltDP.HomComplexComparison.cohomologyClassPostcomp_mk, toHom_mk,
    Cocycle.equivHomShift_symm_postcomp, Functor.map_comp, toHom_mk]

end CochainComplex.HomComplex.CohomologyClass
