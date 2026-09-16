/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import KltDP.Compatibility.HomComplexSingleCocycle
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Cocycles and morphisms to shifted complexes

Port of the right-shift cocycle equivalence and its composition laws from
Mathlib `HomComplexShift` at 79d0395a1825a6264ad5d269e35e60537518955e,
lines 571–608. The original shifts, their inverse and additive laws, and
the degree-zero morphism equivalence are already in the pinned library.
The projection equations below replace generated upstream declarations.
-/

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ} {n : ℤ}

namespace CochainComplex.HomComplex.Cocycle

/-- Right shift gives an additive equivalence on the original cocycles. -/
def rightShiftAddEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cocycle K L n ≃+ Cocycle K (L⟦a⟧) n' where
  toFun γ := γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by
    apply Cocycle.ext
    exact Cochain.rightUnshift_rightShift (γ : Cochain K L n) a n' hn'
  right_inv γ := by
    apply Cocycle.ext
    exact Cochain.rightShift_rightUnshift (γ : Cochain K (L⟦a⟧) n') n hn'
  map_add' γ γ' := by
    apply Cocycle.ext
    exact Cochain.rightShift_add (γ : Cochain K L n) (γ' : Cochain K L n) a n' hn'

@[simp]
lemma rightShiftAddEquiv_apply (n a n' : ℤ) (hn' : n' + a = n)
    (γ : Cocycle K L n) :
    rightShiftAddEquiv n a n' hn' γ = γ.rightShift a n' hn' := rfl

@[simp]
lemma rightShiftAddEquiv_symm_apply (n a n' : ℤ) (hn' : n' + a = n)
    (γ : Cocycle K (L⟦a⟧) n') :
    (rightShiftAddEquiv n a n' hn').symm γ = γ.rightUnshift n hn' := rfl

/-- Morphisms to the shift by `n` identify additively with degree-`n` cocycles. -/
def equivHomShift : (K ⟶ L⟦n⟧) ≃+ Cocycle K L n :=
  (equivHom _ _).trans (rightShiftAddEquiv _ _ _ (zero_add n)).symm

lemma equivHomShift_apply (f : K ⟶ L⟦n⟧) :
    equivHomShift f = (ofHom f).rightUnshift n (zero_add n) := rfl

lemma equivHomShift_symm_apply (z : Cocycle K L n) :
    equivHomShift.symm z = homOf (z.rightShift n 0 (zero_add n)) := rfl

lemma equivHomShift_comp {K' : CochainComplex C ℤ}
    (g : K' ⟶ K) (f : K ⟶ L⟦n⟧) :
    equivHomShift (g ≫ f) = Cocycle.precomp (equivHomShift f) g := by
  ext p q hpq
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

lemma equivHomShift_symm_precomp
    (z : Cocycle K L n) {K' : CochainComplex C ℤ} (g : K' ⟶ K) :
    equivHomShift.symm (z.precomp g) = g ≫ equivHomShift.symm z :=
  equivHomShift.injective (by simp [equivHomShift_comp])

lemma equivHomShift_comp_shift (f : K ⟶ L⟦n⟧)
    {L' : CochainComplex C ℤ} (g : L ⟶ L') :
    equivHomShift (f ≫ g⟦n⟧') = Cocycle.postcomp (equivHomShift f) g := by
  ext p q rfl
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

lemma equivHomShift_symm_postcomp
    (z : Cocycle K L n) {L' : CochainComplex C ℤ} (g : L ⟶ L') :
    equivHomShift.symm (z.postcomp g) = equivHomShift.symm z ≫ g⟦n⟧' :=
  equivHomShift.injective (by simp [equivHomShift_comp_shift])

end CochainComplex.HomComplex.Cocycle
