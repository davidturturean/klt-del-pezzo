/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import KltDP.Geometry.ModuleOpenRestriction
import KltDP.Geometry.SheafPicard
import KltDP.Compatibility.IsomorphicScalarsTensor
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Actual open restriction preserves module-sheaf tensor and unit

The local-bijectivity and sheafification argument is ported from AINTLIB
`160e446617a2168c34c95bbe7a76c4105b392434`,
`projects/ModularCurves/ModularCurves/ForMathlib/PullbackTensorMonoidal.lean`,
lines 219–357. Upstream SHA-256:
`ed4f8dbecf1a053c2faaff60bb04666ff9a502dedeac1aa1263361669b3bb001`.
The Apache-2.0 attribution is retained above. The port uses the actual
restriction functor already constructed for the pinned scheme modules,
and omits the upstream comparison with a general pullback functor.

All tensor products are the project's actual sheafified module tensor.
The unit comparison is the actual section-ring isomorphism of the open
immersion, assembled as a module-sheaf isomorphism. These are object
comparisons sufficient to induce a homomorphism on tensor isomorphism
classes; no full monoidal coherence structure is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

-- These are the original sectionwise tensors over each scheme's
-- commutative structure presheaf, made explicit for the pinned elaborator.
local instance structurePresheafMonoidal (Z : Scheme.{u}) :
    MonoidalCategory (_root_.PresheafOfModules.{u} Z.ringCatSheaf.val) :=
  _root_.PresheafOfModules.monoidalCategory (R := Z.presheaf)

local instance : f.opensFunctor.IsContinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
  f.isOpenEmbedding.functor_isContinuous

/-- A covering sieve pulls back to a covering sieve along the actual
image-open functor of an open immersion. -/
theorem imageFunctor_covering {U : Y.Opens} (S : Sieve (f.opensFunctor.obj U))
    (hS : S ∈ Opens.grothendieckTopology X (f.opensFunctor.obj U)) :
    S.functorPullback f.opensFunctor ∈ Opens.grothendieckTopology Y U := by
  intro y hy
  obtain ⟨W, g, hg, hW⟩ := hS (f.base y) ⟨y, hy, rfl⟩
  refine ⟨f ⁻¹ᵁ W, homOfLE ?_, ?_, hW⟩
  · exact (Scheme.Hom.preimage_image_eq f U) ▸
      (fun a ha => g.le ha : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ (f ''ᵁ U))
  · show S (f.opensFunctor.map _)
    have hle : f.opensFunctor.obj (f ⁻¹ᵁ W) ≤ W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inter]
      exact inf_le_right
    exact Subsingleton.elim (homOfLE hle ≫ g) (f.opensFunctor.map _) ▸
      S.downward_closed hg (homOfLE hle)

/-- Actual open restriction preserves local injectivity. -/
theorem restriction_isLocallyInjective
    {A B : (X.Opens)ᵒᵖ ⥤ AddCommGrp.{u}} (g : A ⟶ B)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) g] :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (CategoryTheory.whiskerLeft f.opensFunctor.op g) := by
  constructor
  intro U x y h
  exact imageFunctor_covering f _
    (Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) g x y h)

/-- Actual open restriction preserves local surjectivity. -/
theorem restriction_isLocallySurjective
    {A B : (X.Opens)ᵒᵖ ⥤ AddCommGrp.{u}} (g : A ⟶ B)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) g] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (CategoryTheory.whiskerLeft f.opensFunctor.op g) := by
  constructor
  intro U t
  exact imageFunctor_covering f _
    (Presheaf.imageSieve_mem (Opens.grothendieckTopology X) g t)

/-- The actual restricted sheafification unit becomes an isomorphism
after sheafification on the actual source scheme. -/
theorem restriction_sheafificationUnit_mem (P : X.PresheafOfModules) :
    PresheafOfModules.sheafificationW (𝟙 Y.ringCatSheaf.val)
      ((PresheafOfModules.pushforward (restrictionRingHom f)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app P)) := by
  rw [PresheafOfModules.sheafificationW_iff_isLocallyBijective]
  constructor
  · change Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (CategoryTheory.whiskerLeft f.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))
    exact restriction_isLocallyInjective f _
  · change Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (CategoryTheory.whiskerLeft f.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))
    exact restriction_isLocallySurjective f _

/-- The actual restriction functor commutes with module sheafification. -/
def restrictionSheafificationIso (P : X.PresheafOfModules) :
    (restriction f).obj ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
        ((PresheafOfModules.pushforward (restrictionRingHom f)).obj P) := by
  have hmem := restriction_sheafificationUnit_mem f P
  rw [PresheafOfModules.sheafificationW_iff] at hmem
  exact (PresheafOfModules.sheafificationForgetIso Y.ringCatSheaf
    ((restriction f).obj
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P))).symm ≪≫
    (@asIso _ _ _ _ _ hmem).symm

local instance (U : (Y.Opens)ᵒᵖ) : IsIso ((restrictionRingHom f).app U) :=
  inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))

-- Keep the presheaf and sheafification boundaries in separate declarations.
-- This prevents elaboration of the final composite from repeatedly unfolding
-- the localized monoidal structure while inferring intermediate objects.
private def restrictionPresheafTensorIso (P Q : X.PresheafOfModules) :
    (PresheafOfModules.pushforward (restrictionRingHom f)).obj (P ⊗ Q) ≅
      (PresheafOfModules.pushforward (restrictionRingHom f)).obj P ⊗
        (PresheafOfModules.pushforward (restrictionRingHom f)).obj Q :=
  (KltDP.PresheafOfModules.pushforwardTensorIso
    (F := f.opensFunctor) (R := X.sheaf.val) (S := Y.sheaf.val)
    (restrictionRingHom f) P Q).symm

set_option maxHeartbeats 800000 in
private def restrictionSheafifiedTensorIso (M N : X.Modules) :
    (restriction f).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj (M.val ⊗ N.val)) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
        (((restriction f).obj M).val ⊗ ((restriction f).obj N).val) := by
  let middle := (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
    ((PresheafOfModules.pushforward (restrictionRingHom f)).obj (M.val ⊗ N.val))
  let first : (restriction f).obj
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj (M.val ⊗ N.val)) ≅
      middle := restrictionSheafificationIso f (M.val ⊗ N.val)
  let second : middle ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
        (((restriction f).obj M).val ⊗ ((restriction f).obj N).val) :=
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).mapIso
      (restrictionPresheafTensorIso f M.val N.val)
  exact first ≪≫ second

set_option maxHeartbeats 800000 in
private def restrictionTensorToSheafificationIso (M N : X.Modules) :
    letI := Scheme.Modules.monoidalCategory X
    (restriction f).obj (M ⊗ N) ≅
      (restriction f).obj
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj (M.val ⊗ N.val)) := by
  letI := Scheme.Modules.monoidalCategory X
  exact (restriction f).mapIso
    (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond M N)

set_option maxHeartbeats 800000 in
private def restrictionTensorFromSheafificationIso (M N : X.Modules) :
    letI := Scheme.Modules.monoidalCategory Y
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
        (((restriction f).obj M).val ⊗ ((restriction f).obj N).val) ≅
      (restriction f).obj M ⊗ (restriction f).obj N := by
  letI := Scheme.Modules.monoidalCategory Y
  exact (PresheafOfModules.sheafTensorIsoSheafification
    Y.sheaf.val Y.ringCatSheaf.cond ((restriction f).obj M) ((restriction f).obj N)).symm

set_option maxHeartbeats 800000 in
/-- The actual open restriction functor preserves the actual sheaf
tensor product, through the proved presheaf and sheafification comparisons. -/
def restrictionTensorIso (M N : X.Modules) :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    (restriction f).obj (M ⊗ N) ≅ (restriction f).obj M ⊗ (restriction f).obj N := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  exact restrictionTensorToSheafificationIso f M N ≪≫
    restrictionSheafifiedTensorIso f M N ≪≫
    restrictionTensorFromSheafificationIso f M N

/-- The actual inverse section-ring comparisons form a presheaf isomorphism. -/
def restrictionRingPresheafIso : Y.presheaf ≅ f.opensFunctor.op ⋙ X.presheaf :=
  NatIso.ofComponents (fun U => (f.appIso U.unop).symm)
    (fun i => f.appIso_inv_naturality i)

/-- The actual section-ring isomorphism is linear for the transported
scalar action on the restricted unit module. -/
def restrictionUnitLinearEquiv (U : Y.Opens) :
    ((restriction f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)).val.obj (op U) ≃ₗ[Γ(Y, U)]
      (_root_.SheafOfModules.unit Y.ringCatSheaf).val.obj (op U) :=
  { (f.appIso U).commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' := fun r s => by
      let s' : Γ(X, f ''ᵁ U) := s
      change (f.appIso U).hom ((f.appIso U).inv r * s') = r * (f.appIso U).hom s'
      rw [map_mul, Iso.inv_hom_id_apply] }

/-- Restriction of the actual ring unit sheaf is the actual ring unit
sheaf of the source scheme. -/
def restrictionUnitIso :
    (restriction f).obj (_root_.SheafOfModules.unit X.ringCatSheaf) ≅
      _root_.SheafOfModules.unit Y.ringCatSheaf :=
  (_root_.SheafOfModules.fullyFaithfulForget Y.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun U => (restrictionUnitLinearEquiv f U.unop).toModuleIso)
      (fun {U V} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact ConcreteCategory.congr_hom ((restrictionRingPresheafIso f).inv.naturality i) s))

/-- Actual restriction preserves the chosen monoidal tensor unit. -/
def restrictionTensorUnitIso :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    (restriction f).obj (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  exact (restriction f).mapIso
      (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond) ≪≫
    restrictionUnitIso f ≪≫
    (PresheafOfModules.sheafTensorUnitIso Y.sheaf.val Y.ringCatSheaf.cond).symm

end KltDP.Geometry.SchemeModuleRestriction
