/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Single

/-!
# Extension of a complex concentrated in one degree

This is the single-complex part of Mathlib's `Embedding.Extend` at commit
79d0395a1825a6264ad5d269e35e60537518955e, adapted to the project's pinned API.
The extension is identified with the single complex at the image degree.
-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroObject C] [HasZeroMorphisms C]
  [DecidableEq ι] (e : c.Embedding c') (X : C)

@[simp]
lemma extend_single_d (i : ι) (j' k' : ι') :
    (((single C c i).obj X).extend e).d j' k' = 0 := by
  by_cases hj : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    by_cases hk : ∃ k, e.f k = k'
    · obtain ⟨k, rfl⟩ := hk
      simp [extend_d_eq _ _ rfl rfl]
    · exact IsZero.eq_of_tgt
        (isZero_extend_X _ _ _ (fun k hk' => hk ⟨k, hk'⟩)) _ _
  · exact IsZero.eq_of_src
      (isZero_extend_X _ _ _ (fun j hj' => hj ⟨j, hj'⟩)) _ _

variable [DecidableEq ι'] (i : ι) (i' : ι')

/-- Extending a single complex moves its nonzero degree along the embedding. -/
noncomputable def extendSingleIso (h : e.f i = i') :
    ((single C c i).obj X).extend e ≅ (single C c' i').obj X where
  hom :=
    mkHomToSingle
      ((((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom)
      (by simp)
  inv :=
    mkHomFromSingle
      ((singleObjXSelf c i X).inv ≫ (((single C c i).obj X).extendXIso e h).inv)
      (by simp)
  hom_inv_id := by
    ext j'
    by_cases hj : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj
      by_cases hij : j = i
      · obtain rfl : i' = j' := by rw [← hj, hij, h]
        simp
      · exact ((isZero_single_obj_X _ _ _ _ hij).of_iso
          (((single C c i).obj X).extendXIso e hj)).eq_of_src _ _
    · exact IsZero.eq_of_src
        (isZero_extend_X _ _ _ (fun j hj' => hj ⟨j, hj'⟩)) _ _
  inv_hom_id := by
    apply from_single_hom_ext
    simp

@[reassoc]
lemma extendSingleIso_hom_f (h : e.f i = i') :
    (extendSingleIso e X i i' h).hom.f i' =
      (((single C c i).obj X).extendXIso e h).hom ≫ (singleObjXSelf c i X).hom ≫
        (singleObjXSelf c' i' X).inv := by
  simp [extendSingleIso]

@[reassoc]
lemma extendSingleIso_inv_f (h : e.f i = i') :
    (extendSingleIso e X i i' h).inv.f i' =
      (singleObjXSelf c' i' X).hom ≫ (singleObjXSelf c i X).inv ≫
        (((single C c i).obj X).extendXIso e h).inv := by
  simp [extendSingleIso]

end HomologicalComplex
