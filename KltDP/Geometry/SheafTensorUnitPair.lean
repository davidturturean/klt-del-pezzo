/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

Adapted from CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/PicComparison.lean, lines 465–647.
The source's tensor and unit wrappers are replaced by the actual pinned
module sheafification and unit sheaf. Sheaf projections and push_neg syntax
are adapted to Lean 4.19. No sectionwise tensor isomorphism is assumed.
-/
import KltDP.Geometry.SheafPicard
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-!
# A local unit pair from an actual sheaf tensor isomorphism

An isomorphism from the sheafified tensor of two actual structure-sheaf
modules to the unit gives, near each point, sections whose pairing is one.
The proof lifts the inverse unit section through sheafification locally,
decomposes a tensor into a finite sum of pure tensors, and uses the actual
local stalk ring to find and rescale a unit pairing value.

This file proves the local pair, not the converse Picard theorem. In
particular it does not replace a sheaf tensor by the tensor of global
sections, or assume that the presheaf evaluation is pointwise invertible.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.SchemeTensorPairing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}}

/-- The actual module sheafification of the presheaf tensor. -/
noncomputable def tensorSheafification (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val)

/-- The actual structure-sheaf module over itself. -/
noncomputable abbrev unitSheaf (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

noncomputable def tensorToSheafify (M N : X.Modules) :
    (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) ⟶ (tensorSheafification M N).val := by
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).unit.app (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val)

theorem tensorToSheafify_app_apply (M N : X.Modules) (V : X.Opens)
    (t : (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V)) :
    (tensorToSheafify M N).app (Opposite.op V) t =
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology ↥X)
        (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).presheaf).app (Opposite.op V) t :=
  rfl

theorem tensorSheafification_val_map_apply (M N : X.Modules) {V W : X.Opens}
    (i : Opposite.op V ⟶ Opposite.op W) (t : (tensorSheafification M N).val.obj (Opposite.op V)) :
    (tensorSheafification M N).val.map i t =
      (CategoryTheory.sheafify (_root_.Opens.grothendieckTopology ↥X)
        (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).presheaf).map i t :=
  rfl

/-- The pairing of an isomorphism `ε : M ⊗ N ≅ 𝒪ₓ` on presheaf-tensor elements over an
open `V`: apply the sheafification unit, then `ε.hom`, landing in `𝒪(V)`. -/
noncomputable def pairingElem {M N : X.Modules} (ε : tensorSheafification M N ≅ unitSheaf X)
    (V : X.Opens)
    (t : ((PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V) :=
  ε.hom.val.app (Opposite.op V) ((tensorToSheafify M N).app (Opposite.op V) t)

/-- The pairing is additive. -/
theorem pairingElem_add {M N : X.Modules} (ε : tensorSheafification M N ≅ unitSheaf X) (V : X.Opens)
    (t t' : ((PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    pairingElem ε V (t + t') = pairingElem ε V t + pairingElem ε V t' := by
  simp only [pairingElem, map_add]

/-- The pairing is homogeneous (both layers are morphisms of modules). -/
theorem pairingElem_smul {M N : X.Modules} (ε : tensorSheafification M N ≅ unitSheaf X) (V : X.Opens)
    (c : (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V))
    (t : ((PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    pairingElem ε V (c • t) = c • pairingElem ε V t := by
  have h₁ := ((tensorToSheafify M N).app (Opposite.op V)).hom.map_smul c t
  have h₂ := (ε.hom.val.app (Opposite.op V)).hom.map_smul c
    ((tensorToSheafify M N).app (Opposite.op V) t)
  exact (congrArg (ε.hom.val.app (Opposite.op V)) h₁).trans h₂

/-- The pairing is additive (both layers are morphisms of modules). -/
theorem pairingElem_sum {M N : X.Modules} (ε : tensorSheafification M N ≅ unitSheaf X) (V : X.Opens)
    {ι : Type*} (s : Finset ι)
    (f : ι → ((PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    pairingElem ε V (∑ i ∈ s, f i) = ∑ i ∈ s, pairingElem ε V (f i) := by
  simp only [pairingElem, map_sum]

/-- The pairing commutes with restriction (naturality of both layers). -/
theorem pairingElem_map {M N : X.Modules} (ε : tensorSheafification M N ≅ unitSheaf X)
    {V W : X.Opens} (i : Opposite.op V ⟶ Opposite.op W)
    (t : ((PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    pairingElem ε W ((PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).map i t) =
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).map i (pairingElem ε V t) := by
  simp only [pairingElem]
  exact (congrArg (ε.hom.val.app (Opposite.op W))
    (PresheafOfModules.naturality_apply (tensorToSheafify M N) i t)).trans
    (PresheafOfModules.naturality_apply ε.hom.val i _)

/-- **[CMP-L2]** Around every point, an isomorphism `ε : M ⊗ N ≅ 𝒪ₓ` yields a section
pair whose pairing is exactly `1`: locally lift the `ε`-preimage of the unit section
through the sheafification, decompose the lift as a finite sum of pure tensors, use
locality of the stalk to find a summand with invertible pairing, then rescale. -/
theorem exists_pairingElem_tmul_eq_one {M N : X.Modules} (ε : tensorSheafification M N ≅ unitSheaf X)
    (x : X) :
    ∃ (V : X.Opens) (_ : x ∈ V) (m : M.val.obj (Opposite.op V))
      (n : N.val.obj (Opposite.op V)), pairingElem ε V (m ⊗ₜ n) = 1 := by
  classical
  -- the ε-preimage of the unit section
  set ζ := ε.inv.val.app (Opposite.op ⊤)
    (show (unitSheaf X).val.obj (Opposite.op ⊤) from
      (1 : X.ringCatSheaf.val.obj (Opposite.op ⊤))) with hζ
  -- locally lift ζ through the sheafification unit
  have hmem : Presheaf.imageSieve (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology ↥X)
      (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
        (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).presheaf) ζ ∈
      _root_.Opens.grothendieckTopology ↥X ⊤ :=
    Presheaf.imageSieve_mem (_root_.Opens.grothendieckTopology ↥X)
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology ↥X)
        (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.val) M.val N.val : _root_.PresheafOfModules
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).presheaf) (U := Opposite.op ⊤) ζ
  obtain ⟨V₀, iV₀, hlift, hxV₀⟩ := hmem x trivial
  obtain ⟨τ, hτ⟩ := hlift
  -- ε sends ζ back to the unit section
  have hcomp : ε.inv.val ≫ ε.hom.val = 𝟙 _ :=
    congrArg SheafOfModules.Hom.val ε.inv_hom_id
  have hεone : ε.hom.val.app (Opposite.op ⊤) ζ =
      (show (unitSheaf X).val.obj (Opposite.op ⊤) from
        (1 : X.ringCatSheaf.val.obj (Opposite.op ⊤))) := by
    rw [hζ]
    show (ConcreteCategory.hom ((ε.inv.val ≫ ε.hom.val).app (Opposite.op ⊤)))
      (show (unitSheaf X).val.obj (Opposite.op ⊤) from
        (1 : X.ringCatSheaf.val.obj (Opposite.op ⊤))) = _
    rw [hcomp]
    rfl
  -- the pairing of the lifted section is exactly 1
  have h1 : pairingElem ε V₀ τ = 1 := by
    show ε.hom.val.app (Opposite.op V₀)
      ((tensorToSheafify M N).app (Opposite.op V₀) τ) = _
    have h2 : (tensorToSheafify M N).app (Opposite.op V₀) τ =
        (tensorSheafification M N).val.map iV₀.op ζ := by
      exact (tensorToSheafify_app_apply M N V₀ τ).trans
        (hτ.trans (tensorSheafification_val_map_apply M N iV₀.op ζ).symm)
    refine (congrArg (ε.hom.val.app (Opposite.op V₀)) h2).trans
      ((PresheafOfModules.naturality_apply ε.hom.val iV₀.op ζ).trans
        ((congrArg (X.ringCatSheaf.val.map iV₀.op) hεone).trans ?_))
    show (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).map iV₀.op
      (show (unitSheaf X).val.obj (Opposite.op ⊤) from
        (1 : X.ringCatSheaf.val.obj (Opposite.op ⊤))) = 1
    exact map_one (ConcreteCategory.hom
      ((X.sheaf.val ⋙ forget₂ CommRingCat RingCat).map iV₀.op))
  -- decompose the lift as a finite sum of pure tensors
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset τ
  have h1' : (1 : (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V₀)) =
      ∑ p ∈ S, pairingElem ε V₀ (p.1 ⊗ₜ p.2) :=
    (h1.symm.trans (congrArg (pairingElem ε V₀) hS)).trans (pairingElem_sum ε V₀ S _)
  -- some summand has a pairing with invertible germ at x
  have hpigeon : ∃ p ∈ S,
      IsUnit (X.presheaf.germ V₀ x hxV₀ (pairingElem ε V₀ (p.1 ⊗ₜ p.2))) := by
    by_contra hall
    push_neg at hall
    have hnon : X.presheaf.germ V₀ x hxV₀
        (∑ p ∈ S, pairingElem ε V₀ (p.1 ⊗ₜ p.2)) ∈ nonunits (X.presheaf.stalk x) := by
      rw [map_sum]
      refine Finset.sum_induction _ (· ∈ nonunits _)
        (fun a b ha hb => IsLocalRing.nonunits_add ha hb)
        (zero_mem_nonunits.mpr zero_ne_one) (fun p hp => mem_nonunits_iff.mpr (hall p hp))
    let a : X.presheaf.obj (Opposite.op V₀) :=
      ∑ p ∈ S, pairingElem ε V₀ (p.1 ⊗ₜ p.2)
    have ha : (1 : X.presheaf.obj (Opposite.op V₀)) = a := h1'
    have hnonA : X.presheaf.germ V₀ x hxV₀ a ∈ nonunits (X.presheaf.stalk x) := by
      simpa only [a] using hnon
    have hga : X.presheaf.germ V₀ x hxV₀ a = 1 := by
      rw [← map_one (ConcreteCategory.hom (X.presheaf.germ V₀ x hxV₀)), ha]
    exact (mem_nonunits_iff.mp hnonA) (hga.symm ▸ isUnit_one)
  obtain ⟨p, hpS, hpu⟩ := hpigeon
  -- the unit germ restricts to a unit on a smaller open
  obtain ⟨V, iV, hxV, hu⟩ :=
    X.toLocallyRingedSpace.toRingedSpace.isUnit_res_of_isUnit_germ V₀
      (pairingElem ε V₀ (p.1 ⊗ₜ p.2)) x hxV₀ hpu
  obtain ⟨b, hb⟩ := hu.exists_left_inv
  let c : (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V) := b
  let m₁ : M.val.obj (Opposite.op V) := M.val.map iV.op p.1
  let n₁ : N.val.obj (Opposite.op V) := N.val.map iV.op p.2
  letI : Module ↑((X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V))
      ↑(M.val.obj (Opposite.op V)) :=
    inferInstanceAs (Module ↑(X.ringCatSheaf.val.obj (Opposite.op V))
      ↑(M.val.obj (Opposite.op V)))
  letI : Module ↑((X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V))
      ↑(N.val.obj (Opposite.op V)) :=
    inferInstanceAs (Module ↑(X.ringCatSheaf.val.obj (Opposite.op V))
      ↑(N.val.obj (Opposite.op V)))
  refine ⟨V, hxV, m₁, c • n₁, ?_⟩
  -- rescaling computation
  have hbal : m₁ ⊗ₜ[
        (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)]
        (c • n₁) =
      c • (m₁ ⊗ₜ[
        (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁) :=
    TensorProduct.tmul_smul _ _ _
  have hres : pairingElem ε V
        (m₁ ⊗ₜ[(X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁) =
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).map iV.op
        (pairingElem ε V₀ (p.1 ⊗ₜ p.2)) :=
    (congrArg (pairingElem ε V)
      (PresheafOfModules.Monoidal.tensorObj_map_tmul iV.op p.1 p.2).symm).trans
      (pairingElem_map ε iV.op (p.1 ⊗ₜ p.2))
  have hsm := pairingElem_smul ε V c
    (m₁ ⊗ₜ[
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁)
  calc pairingElem ε V
        (m₁ ⊗ₜ[
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] (c • n₁))
      = pairingElem ε V (c •
          (m₁ ⊗ₜ[
            (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁)) :=
        congrArg (pairingElem ε V) hbal
    _ = c • pairingElem ε V
          (m₁ ⊗ₜ[
            (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁) := hsm
    _ = c • (X.sheaf.val ⋙ forget₂ CommRingCat RingCat).map iV.op
          (pairingElem ε V₀ (p.1 ⊗ₜ p.2)) :=
        congrArg (c • ·) hres
    _ = 1 := (smul_eq_mul c _).trans hb


end KltDP.Geometry.SchemeTensorPairing
