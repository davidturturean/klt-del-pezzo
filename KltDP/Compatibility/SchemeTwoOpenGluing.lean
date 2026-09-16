/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

The two-index GlueData' construction is adapted from the actual two-chart
application in Vilin97/MazurTheorem, commit
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/AlgebraicGeometry/XOneThirteenProjectiveCurve.lean:493-626.
Here the overlap is a common scheme and its transitions are identities.
The generic descent and pullback adapters are local additions using pinned
Mathlib gluing and colimit theorems.
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Gluing two actual schemes along a common open subscheme

This is a narrow interface to existing scheme gluing. The inputs are two
actual open immersions from the same overlap scheme. There are no supplied
glued objects, lifts, coverage conclusions, or intersection identities.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.SchemeTwoOpenGluing

inductive Side : Type u
  | left
  | right

instance : DecidableEq Side.{u} := fun i j => by
  cases i <;> cases j
  · exact isTrue rfl
  · exact isFalse (fun h => by cases h)
  · exact isFalse (fun h => by cases h)
  · exact isTrue rfl

private theorem left_ne_right : (Side.left : Side.{u}) ≠ Side.right := by
  intro h
  cases h

private theorem right_ne_left : (Side.right : Side.{u}) ≠ Side.left := by
  intro h
  cases h

variable {A B W : Scheme.{u}} (f : W ⟶ A) (g : W ⟶ B)
    [IsOpenImmersion f] [IsOpenImmersion g]

abbrev piece : Side.{u} → Scheme.{u}
  | .left => A
  | .right => B

def overlapInclusion : ∀ i : Side.{u}, W ⟶ piece (A := A) (B := B) i
  | .left => f
  | .right => g

instance overlapInclusion_isOpenImmersion (i : Side.{u}) :
    IsOpenImmersion (overlapInclusion f g i) := by
  cases i <;> dsimp [overlapInclusion] <;> infer_instance

/-- Existing categorical glue data; three pairwise distinct sides cannot occur. -/
def categoricalData : CategoryTheory.GlueData' Scheme.{u} where
  J := Side.{u}
  U := piece (A := A) (B := B)
  V _ _ _ := W
  f i _ _ := overlapInclusion f g i
  f_mono _ _ _ := inferInstance
  f_hasPullback _ _ _ _ _ := inferInstance
  t _ _ _ := 𝟙 W
  t' := by
    intro i j k hij hik hjk
    cases i <;> cases j <;> cases k <;> contradiction
  t_fac := by
    intro i j k hij hik hjk
    cases i <;> cases j <;> cases k <;> contradiction
  t_inv _ _ _ := Category.id_comp _
  cocycle := by
    intro i j k hij hik hjk
    cases i <;> cases j <;> cases k <;> contradiction

theorem categoricalData_f_open (i j : Side.{u}) :
    IsOpenImmersion ((categoricalData f g).f' i j) := by
  classical
  dsimp only [CategoryTheory.GlueData'.f']
  split_ifs
  · infer_instance
  · dsimp only [categoricalData]
    infer_instance

/-- Actual scheme gluing, using the existing scheme structure on the colimit. -/
def data : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (categoricalData f g)
  f_open := categoricalData_f_open f g

/-- The off-diagonal overlap object in the library's glue data is
canonically identified with the prescribed common overlap scheme. -/
def overlapObjectIso (i j : Side.{u}) (hij : i ≠ j) : W ≅ (data f g).V (i, j) :=
  eqToIso (by
    dsimp only [data, CategoryTheory.GlueData.ofGlueData', categoricalData]
    simp only [dif_neg hij])

@[reassoc] theorem overlapObjectIso_hom_f (i j : Side.{u}) (hij : i ≠ j) :
    (overlapObjectIso f g i j hij).hom ≫ (data f g).f i j = overlapInclusion f g i := by
  dsimp only [overlapObjectIso, eqToIso, data, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', categoricalData]
  simp only [dif_neg hij, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp]

@[reassoc] theorem overlapObjectIso_hom_t_f (i j : Side.{u}) (hij : i ≠ j) :
    (overlapObjectIso f g i j hij).hom ≫ (data f g).t i j ≫ (data f g).f j i =
      overlapInclusion f g j := by
  dsimp only [overlapObjectIso, eqToIso, data, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', categoricalData]
  simp only [dif_neg hij, dif_neg hij.symm, Category.assoc, Category.id_comp,
    Category.comp_id, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl]

abbrev glued := (data f g).glued

def leftι : A ⟶ glued f g := (data f g).ι .left
def rightι : B ⟶ glued f g := (data f g).ι .right

instance leftι_isOpenImmersion : IsOpenImmersion (leftι f g) := by
  unfold leftι
  infer_instance

instance rightι_isOpenImmersion : IsOpenImmersion (rightι f g) := by
  unfold rightι
  infer_instance

/-- The prescribed common overlap is identified by the actual gluing. -/
theorem overlap_condition : f ≫ leftι f g = g ≫ rightι f g := by
  have h := congrArg
    (fun z => (overlapObjectIso f g Side.left Side.right left_ne_right).hom ≫ z)
    ((data f g).glue_condition Side.left Side.right).symm
  simpa only [Category.assoc, overlapObjectIso_hom_f_assoc, overlapObjectIso_hom_t_f_assoc,
    overlapInclusion, leftι, rightι] using h

/-- The inclusions actually cover the constructed scheme. -/
theorem jointly_surjective (x : glued f g) :
    (∃ a : A, (leftι f g).base a = x) ∨ (∃ b : B, (rightι f g).base b = x) := by
  obtain ⟨i, y, hy⟩ := (data f g).ι_jointly_surjective x
  cases i
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

def toTarget {X : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X)
    (h : f ≫ a = g ≫ b) : glued f g ⟶ X := by
  let k : ∀ i : Side.{u}, piece (A := A) (B := B) i ⟶ X
    | .left => a
    | .right => b
  refine Multicoequalizer.desc (data f g).toGlueData.diagram X k ?_
  rintro ⟨i, j⟩
  change (data f g).f i j ≫ k i = ((data f g).t i j ≫ (data f g).f j i) ≫ k j
  cases i <;> cases j
  · rw [(data f g).t_id, Category.id_comp]
  · apply (cancel_epi (overlapObjectIso f g Side.left Side.right left_ne_right).hom).mp
    simpa only [Category.assoc, overlapObjectIso_hom_f_assoc, overlapObjectIso_hom_t_f_assoc,
      overlapInclusion, k] using h
  · apply (cancel_epi (overlapObjectIso f g Side.right Side.left right_ne_left).hom).mp
    simpa only [Category.assoc, overlapObjectIso_hom_f_assoc, overlapObjectIso_hom_t_f_assoc,
      overlapInclusion, k] using h.symm
  · rw [(data f g).t_id, Category.id_comp]

@[simp] theorem leftι_toTarget {X : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X)
    (h : f ≫ a = g ≫ b) : leftι f g ≫ toTarget f g a b h = a := by
  unfold leftι toTarget
  apply Multicoequalizer.π_desc

@[simp] theorem rightι_toTarget {X : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X)
    (h : f ≫ a = g ≫ b) : rightι f g ≫ toTarget f g a b h = b := by
  unfold rightι toTarget
  apply Multicoequalizer.π_desc

/-- Actual maps out of the constructed scheme are determined by their two restrictions. -/
theorem hom_ext {X : Scheme.{u}} (a b : glued f g ⟶ X)
    (hA : leftι f g ≫ a = leftι f g ≫ b)
    (hB : rightι f g ≫ a = rightι f g ≫ b) : a = b := by
  apply (data f g).openCover.hom_ext
  intro i
  cases i
  · exact hA
  · exact hB

/-- The common overlap is the actual scheme-theoretic intersection of the two pieces. -/
def overlapIsPullback : IsPullback f g (leftι f g) (rightι f g) := by
  have h : IsPullback ((data f g).f Side.left Side.right)
      ((data f g).t Side.left Side.right ≫ (data f g).f Side.right Side.left)
      (leftι f g) (rightι f g) :=
    IsPullback.of_isLimit ((data f g).vPullbackConeIsLimit Side.left Side.right)
  let e := overlapObjectIso f g Side.left Side.right left_ne_right
  apply h.of_iso e.symm (Iso.refl A) (Iso.refl B) (Iso.refl (glued f g))
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact overlapObjectIso_hom_f f g Side.left Side.right left_ne_right
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact overlapObjectIso_hom_t_f f g Side.left Side.right left_ne_right
  · change leftι f g ≫ 𝟙 (glued f g) = 𝟙 A ≫ leftι f g
    exact (Category.comp_id (leftι f g)).trans (Category.id_comp (leftι f g)).symm
  · change rightι f g ≫ 𝟙 (glued f g) = 𝟙 B ≫ rightι f g
    exact (Category.comp_id (rightι f g)).trans (Category.id_comp (rightι f g)).symm

end KltDP.SchemeTwoOpenGluing
