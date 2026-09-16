/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors

The componentwise unique-gluing proof is adapted from
frenzymath/Algebraic-Geometry 9223d85c786394721963a9d642b08d066b72a594,
MainProjects/AlgebraicJacobian/PicardAlbanese/AlgebraicJacobian/Cohomology/
GluedSheaf.lean:195–269. It uses the original structure sheaf as an additive
sheaf, and retains the actual local section-ring actions from
TransitionUnitSections. No external package is imported.
-/
import KltDP.Geometry.TransitionUnitSections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Tactic.Choose

/-!
# The actual module sheaf of matching transition sections

Each component of a compatible family glues in the original structure sheaf.
The transition equations hold for the glued components because they hold
locally. The resulting additive sheaf carries the already constructed action
of the original section rings, giving an actual object of `X.Modules`.

No sheaf condition, chart trivialization, or invertibility is assumed. The
sheaf construction works for arbitrary transition multipliers; cocycle and
covering hypotheses enter the separate local-triviality argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

variable (X : Scheme.{u})

/-- The original structure sheaf, forgetting only to additive groups. -/
private def structureAdditiveSheaf :
    TopCat.Sheaf AddCommGrp.{u} (X : TopCat) :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ RingCat.{u} AddCommGrp.{u})).obj X.ringCatSheaf

variable {ι : Type u} (U : ι → X.Opens) (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)

/-- Matching section families satisfy the sheaf condition by componentwise gluing. -/
theorem isSheaf_additivePresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (additivePresheaf X U g) := by
  classical
  have h : TopCat.Presheaf.IsSheaf (C := AddCommGrp.{u}) (X := (X : TopCat))
      (additivePresheaf X U g) := by
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
    intro κ W sf hsf
    have hres : ∀ a b : κ,
        restrict X U g (inf_le_left : W a ⊓ W b ≤ W a) (sf a) =
          restrict X U g (inf_le_right : W a ⊓ W b ≤ W b) (sf b) :=
      fun a b => hsf a b
    have hcov : ∀ j : ι, (iSup W) ⊓ U j ≤ ⨆ a, W a ⊓ U j := fun j => by
      rw [iSup_inf_eq]
    have hcompat : ∀ j : ι,
        TopCat.Presheaf.IsCompatible (structureAdditiveSheaf X).val
          (fun a => W a ⊓ U j) (fun a => (sf a).val j) := by
      intro j a b
      have key := congrArg (fun q : sections X U g (W a ⊓ W b) =>
        res X (le_inf
          (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          (inf_le_left.trans inf_le_right) :
            (W a ⊓ U j) ⊓ (W b ⊓ U j) ≤ (W a ⊓ W b) ⊓ U j) (q.val j)) (hres a b)
      simp only [restrict_val, res_res] at key
      exact key
    have H : ∀ j : ι, ∃! tj : Γ(X, (iSup W) ⊓ U j),
        ∀ a : κ, res X (inf_le_inf_right (U j) (le_iSup W a)) tj = (sf a).val j := by
      intro j
      obtain ⟨tj, htj, htju⟩ := TopCat.Sheaf.existsUnique_gluing'
        (X := (X : TopCat)) (C := AddCommGrp.{u}) (structureAdditiveSheaf X)
        (fun a => W a ⊓ U j) ((iSup W) ⊓ U j)
        (fun a => homOfLE (inf_le_inf_right (U j) (le_iSup W a))) (hcov j)
        (fun a => (sf a).val j) (hcompat j)
      exact ⟨tj, fun a => htj a, fun y hy => htju y fun a => hy a⟩
    choose t ht htu using H
    have hrel : t ∈ sections X U g (iSup W) := by
      intro i j
      have hcovΩ : (iSup W) ⊓ U i ⊓ U j ≤ ⨆ a, W a ⊓ U i ⊓ U j := by
        rw [iSup_inf_eq, iSup_inf_eq]
      apply TopCat.Sheaf.eq_of_locally_eq' (X := (X : TopCat)) (C := AddCommGrp.{u})
        (structureAdditiveSheaf X) (fun a => W a ⊓ U i ⊓ U j)
        ((iSup W) ⊓ U i ⊓ U j)
        (fun a => homOfLE
          (inf_le_inf_right (U j) (inf_le_inf_right (U i) (le_iSup W a)))) hcovΩ
      intro a
      change res X (inf_le_inf_right (U j) (inf_le_inf_right (U i) (le_iSup W a)))
          (res X inf_le_left (t i)) =
        res X (inf_le_inf_right (U j) (inf_le_inf_right (U i) (le_iSup W a)))
          (res X (inclCoc X U (iSup W) i j) (g i j) *
            res X (inclSnd X U (iSup W) i j) (t j))
      have hloc := (mem_sections_iff X U g (W a) ((sf a).val :
        ∀ l : ι, Γ(X, W a ⊓ U l))).mp (sf a).property i j
      have hti := congrArg
        (res X (inf_le_left : W a ⊓ U i ⊓ U j ≤ W a ⊓ U i)) (ht i a)
      have htj := congrArg (res X (inclSnd X U (W a) i j)) (ht j a)
      rw [map_mul]
      simp only [res_res] at hti htj hloc ⊢
      rw [← hti, ← htj] at hloc
      exact hloc
    refine ⟨⟨t, hrel⟩, fun a => ?_, fun s hs => ?_⟩
    · exact Subtype.ext (funext fun j => ht j a)
    · have hs' : ∀ a, restrict X U g (le_iSup W a) s = sf a := fun a => hs a
      refine Subtype.ext (funext fun j => ?_)
      refine htu j (s.val j) fun a => ?_
      rw [← hs' a, restrict_val]
  exact h

/-- The matching families with the original section-ring module structures. -/
def modulePresheaf : X.PresheafOfModules := by
  letI : ∀ W : (X.Opens)ᵒᵖ,
      Module (X.ringCatSheaf.val.obj W) ((additivePresheaf X U g).obj W) :=
    fun W => inferInstanceAs (Module Γ(X, W.unop) (sections X U g W.unop))
  exact _root_.PresheafOfModules.ofPresheaf (R := X.ringCatSheaf.val)
    (additivePresheaf X U g)
    (fun {V W} f r s => restrict_smul X U g f.unop.le r s)

@[simp]
theorem modulePresheaf_presheaf :
    (modulePresheaf X U g).presheaf = additivePresheaf X U g := rfl

/-- The actual sheaf of modules associated with the matching section families. -/
def moduleSheaf : X.Modules where
  val := modulePresheaf X U g
  isSheaf := isSheaf_additivePresheaf X U g

@[simp]
theorem moduleSheaf_val : (moduleSheaf X U g).val = modulePresheaf X U g := rfl

@[simp]
theorem moduleSheaf_map_apply {V W : X.Opens} (h : V ≤ W) (s : sections X U g W) :
    (moduleSheaf X U g).val.map (homOfLE h).op s = restrict X U g h s := rfl

end KltDP.Geometry.TransitionUnitGluing
