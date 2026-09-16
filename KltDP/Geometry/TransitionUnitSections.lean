/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors

Adapted from frenzymath/Algebraic-Geometry
9223d85c786394721963a9d642b08d066b72a594,
PicardAlbanese/AlgebraicJacobian/Cohomology/GluedSheaf.lean and
GluedSheafQcoh.lean. The matching families and their original section-ring
actions are retained; no external package is imported.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Ring

/-!
# Actual matching sections for a unit cocycle

For actual opens Uᵢ and actual units gᵢⱼ on their intersections, sections
over W are families on W ∩ Uᵢ satisfying the original transition equations.
The original ring O(W) acts by restriction and componentwise multiplication.
These actions commute with the actual restriction maps.

The carrier and presheaf require no cocycle law. The subsequent local
trivializations use the explicitly stated normalization and triple-overlap
identities; the subsequent sheaf proof glues in the structure sheaf itself.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

variable (X : Scheme.{u})

/-- The original structure-sheaf restriction, exposed as a ring homomorphism. -/
def res {V W : X.Opens} (h : V ≤ W) : Γ(X, W) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

@[simp]
theorem res_self (W : X.Opens) (s : Γ(X, W)) : res X (le_refl W) s = s := by
  change (X.presheaf.map (𝟙 (op W))).hom s = s
  rw [X.presheaf.map_id]
  rfl

theorem res_res {V W Z : X.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z) (s : Γ(X, Z)) :
    res X hVW (res X hWZ s) = res X (hVW.trans hWZ) s := by
  have h := congrArg (fun f : Γ(X, Z) →+* Γ(X, V) => f s)
    (congrArg CommRingCat.Hom.hom
      (X.presheaf.map_comp (homOfLE hWZ).op (homOfLE hVW).op))
  exact h.symm

variable {ι : Type u} (U : ι → X.Opens)

def inclSnd (W : X.Opens) (i j : ι) : W ⊓ U i ⊓ U j ≤ W ⊓ U j :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

def inclCoc (W : X.Opens) (i j : ι) : W ⊓ U i ⊓ U j ≤ U i ⊓ U j :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

variable (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)

/-- Normalized transition units satisfying the actual triple-overlap equation. -/
structure IsCocycle : Prop where
  unit_self : ∀ i, (g i i : Γ(X, U i ⊓ U i)) = 1
  mul_res : ∀ i j l,
    res X (inf_le_left : U i ⊓ U j ⊓ U l ≤ U i ⊓ U j) (g i j) *
      res X (inclCoc X U (U i) j l) (g j l) =
        res X (inclSnd X U (U i) j l) (g i l)

theorem IsCocycle.mul_res_of_le (hc : IsCocycle X U g)
    {i j l : ι} {W : X.Opens} (hW : W ≤ U i ⊓ U j ⊓ U l) :
    res X (hW.trans inf_le_left) (g i j) *
      res X (hW.trans (inclCoc X U (U i) j l)) (g j l) =
        res X (hW.trans (inclSnd X U (U i) j l)) (g i l) := by
  have h := congrArg (res X hW) (hc.mul_res i j l)
  rw [map_mul] at h
  simpa only [res_res] using h

/-- The additive group of actual matching section families. -/
def sections (W : X.Opens) : AddSubgroup (∀ i : ι, Γ(X, W ⊓ U i)) where
  carrier := {s | ∀ i j,
    res X (inf_le_left : W ⊓ U i ⊓ U j ≤ W ⊓ U i) (s i) =
      res X (inclCoc X U W i j) (g i j) * res X (inclSnd X U W i j) (s j)}
  zero_mem' := by
    intro i j
    change res X _ 0 = _ * res X _ 0
    rw [map_zero, map_zero, mul_zero]
  add_mem' := by
    intro s t hs ht i j
    change res X _ (s i + t i) = _ * res X _ (s j + t j)
    rw [map_add, map_add, mul_add, hs i j, ht i j]
  neg_mem' := by
    intro s hs i j
    change res X _ (-s i) = _ * res X _ (-s j)
    rw [map_neg, map_neg, hs i j, mul_neg]

theorem mem_sections_iff (W : X.Opens) (s : ∀ i : ι, Γ(X, W ⊓ U i)) :
    s ∈ sections X U g W ↔ ∀ i j,
      res X (inf_le_left : W ⊓ U i ⊓ U j ≤ W ⊓ U i) (s i) =
        res X (inclCoc X U W i j) (g i j) * res X (inclSnd X U W i j) (s j) := Iff.rfl

/-- Multiplication by the actual restriction of a section of O(W). -/
def sectionSMul (W : X.Opens) (r : Γ(X, W)) (s : sections X U g W) : sections X U g W :=
  ⟨fun i => res X (inf_le_left : W ⊓ U i ≤ W) r * s.val i, by
    intro i j
    change res X _ (res X _ r * s.val i) = _ * res X _ (res X _ r * s.val j)
    rw [map_mul, map_mul]
    simp only [res_res]
    rw [s.property i j]
    ring⟩

instance sectionsModule (W : X.Opens) : Module Γ(X, W) (sections X U g W) where
  smul := sectionSMul X U g W
  one_smul s := by
    apply Subtype.ext
    funext i
    change res X _ 1 * s.val i = s.val i
    rw [map_one, one_mul]
  mul_smul r t s := by
    apply Subtype.ext
    funext i
    change res X _ (r * t) * s.val i = res X _ r * (res X _ t * s.val i)
    rw [map_mul, mul_assoc]
  smul_zero r := by
    apply Subtype.ext
    funext i
    change res X _ r * 0 = 0
    exact mul_zero _
  smul_add r s t := by
    apply Subtype.ext
    funext i
    change res X _ r * (s.val i + t.val i) = res X _ r * s.val i + res X _ r * t.val i
    exact mul_add _ _ _
  add_smul r t s := by
    apply Subtype.ext
    funext i
    change res X _ (r + t) * s.val i = res X _ r * s.val i + res X _ t * s.val i
    rw [map_add, add_mul]
  zero_smul s := by
    apply Subtype.ext
    funext i
    change res X _ 0 * s.val i = 0
    rw [map_zero, zero_mul]

@[simp]
theorem smul_val (W : X.Opens) (r : Γ(X, W)) (s : sections X U g W) (i : ι) :
    ((r • s : sections X U g W).val i) =
      res X (inf_le_left : W ⊓ U i ≤ W) r * s.val i := rfl

/-- The matching condition is preserved by componentwise restriction. -/
theorem sections_restrict {V W : X.Opens} (h : V ≤ W)
    {s : ∀ i : ι, Γ(X, W ⊓ U i)} (hs : s ∈ sections X U g W) :
    (fun i => res X (inf_le_inf_right (U i) h) (s i)) ∈ sections X U g V := by
  intro i j
  have key := congrArg
    (res X (inf_le_inf_right (U j) (inf_le_inf_right (U i) h))) (hs i j)
  rw [map_mul] at key
  simpa only [res_res] using key

/-- The original componentwise restrictions of the matched sections. -/
def restrict {V W : X.Opens} (h : V ≤ W) : sections X U g W →+ sections X U g V where
  toFun s := ⟨fun i => res X (inf_le_inf_right (U i) h) (s.val i),
    sections_restrict X U g h s.property⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    exact map_zero _
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact map_add _ _ _

@[simp]
theorem restrict_val {V W : X.Opens} (h : V ≤ W) (s : sections X U g W) (i : ι) :
    (restrict X U g h s).val i = res X (inf_le_inf_right (U i) h) (s.val i) := rfl

theorem restrict_self (W : X.Opens) (s : sections X U g W) :
    restrict X U g (le_refl W) s = s := by
  apply Subtype.ext
  funext i
  exact res_self X (W ⊓ U i) (s.val i)

theorem restrict_restrict {V W Z : X.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z)
    (s : sections X U g Z) :
    restrict X U g hVW (restrict X U g hWZ s) = restrict X U g (hVW.trans hWZ) s := by
  apply Subtype.ext
  funext i
  exact res_res X (inf_le_inf_right (U i) hVW) (inf_le_inf_right (U i) hWZ) (s.val i)

/-- The scalar action commutes with the actual restriction ring homomorphism. -/
theorem restrict_smul {V W : X.Opens} (h : V ≤ W) (r : Γ(X, W))
    (s : sections X U g W) :
    restrict X U g h (r • s) = res X h r • restrict X U g h s := by
  apply Subtype.ext
  funext i
  change res X _ (res X _ r * s.val i) = res X _ (res X h r) * res X _ (s.val i)
  rw [map_mul]
  simp only [res_res]

/-- The actual additive presheaf of matching families. -/
def additivePresheaf : (X.Opens)ᵒᵖ ⥤ AddCommGrp.{u} where
  obj W := AddCommGrp.of (sections X U g W.unop)
  map i := AddCommGrp.ofHom (restrict X U g i.unop.le)
  map_id W := by
    apply AddCommGrp.hom_ext
    exact AddMonoidHom.ext (fun s => restrict_self X U g W.unop s)
  map_comp i j := by
    apply AddCommGrp.hom_ext
    exact AddMonoidHom.ext
      (fun s => (restrict_restrict X U g j.unop.le i.unop.le s).symm)

end KltDP.Geometry.TransitionUnitGluing
