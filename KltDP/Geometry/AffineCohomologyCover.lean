/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Adapted from Vilin97/MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SchemeModuleCohomologyAffineCover.lean:139-182 and
SchemeModuleCohomologyAffineCoverMono.lean:37-110.
The original project restriction, pushforward, and adjunction replace
the modern Scheme.Modules APIs. The actual product and cokernel remain.
-/
import KltDP.Geometry.AffineCohomologyFiniteProducts
import KltDP.Geometry.AffineCohomologyPushforward
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Topology.Sets.OpenCover

/-!
# The actual affine-cover module and its short exact sequence

The product of actual restriction-pushforwards is quasicoherent for a
finite affine family. Its adjunction-unit map is monic whenever the
opens cover. This supplies the original quasicoherent cokernel used in
the affine-vanishing proof. Source draft; VM checks pending.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineCohomologyPort

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem image_preimage_le {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (W : X.Opens) : f ''ᵁ f ⁻¹ᵁ W ≤ W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter]
  exact inf_le_right

/-- The unit is the original restriction to the image of the preimage open. -/
theorem restrictionUnit_app {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (W : X.Opens) (s : M.val.obj (op W)) :
    ((SchemeModuleRestriction.restrictionAdjunction f).unit.app M).val.app (op W) s =
      M.val.map (homOfLE (image_preimage_le f W)).op s := by
  change M.val.map (f.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op s = _
  exact congrArg (fun a : f ''ᵁ f ⁻¹ᵁ W ⟶ W => M.val.map a.op s)
    (Subsingleton.elim _ _)

/-- The actual product of the restriction-pushforwards of a scheme module. -/
def affineCoverModule {X : Scheme.{u}} {I : Type u}
    (M : X.Modules) (U : I → X.Opens) : X.Modules :=
  ∏ᶜ fun i => (SchemeModuleRestriction.restriction (U i).ι ⋙
    schemeModulePushforward (U i).ι).obj M

/-- The original adjunction units give the actual cover map. -/
def toAffineCoverModule {X : Scheme.{u}} {I : Type u}
    (M : X.Modules) (U : I → X.Opens) : M ⟶ affineCoverModule M U :=
  Pi.lift fun i => (SchemeModuleRestriction.restrictionAdjunction (U i).ι).unit.app M

/-- Projection to each factor is the original restriction-adjunction unit. -/
theorem toAffineCoverModule_comp_pi {X : Scheme.{u}} {I : Type u}
    (M : X.Modules) (U : I → X.Opens) (i : I) :
    toAffineCoverModule M U ≫
      Pi.π (fun i => (SchemeModuleRestriction.restriction (U i).ι ⋙
        schemeModulePushforward (U i).ι).obj M) i =
      (SchemeModuleRestriction.restrictionAdjunction (U i).ι).unit.app M := by
  simp [toAffineCoverModule, affineCoverModule]

/-- The finite affine cover product is quasicoherent on the original spectrum. -/
theorem affineCoverModule_isQuasicoherent {R : Type u} [CommRing R]
    {I : Type u} [Finite I] (M : (Spec (.of R)).Modules) [M.IsQuasicoherent]
    (U : I → (Spec (.of R)).Opens) [∀ i, IsAffine (U i)] :
    (affineCoverModule M U).IsQuasicoherent := by
  letI (i : I) : ((SchemeModuleRestriction.restriction (U i).ι ⋙
      schemeModulePushforward (U i).ι).obj M).IsQuasicoherent :=
    pushforward_isQuasicoherent_of_affine (U i).ι
      ((SchemeModuleRestriction.restriction (U i).ι).obj M)
  exact product_isQuasicoherent _

/-- Its ambient categorical cokernel is quasicoherent. -/
theorem affineCoverCokernel_isQuasicoherent {R : Type u} [CommRing R]
    {I : Type u} [Finite I] (M : (Spec (.of R)).Modules) [M.IsQuasicoherent]
    (U : I → (Spec (.of R)).Opens) [∀ i, IsAffine (U i)] :
    (cokernel (toAffineCoverModule M U)).IsQuasicoherent := by
  letI := affineCoverModule_isQuasicoherent M U
  exact AffineModuleTilde.cokernel_isQuasicoherent (toAffineCoverModule M U)

/-- The actual cover map is injective on every original section group. -/
theorem toAffineCoverModule_app_injective {X : Scheme.{u}} {I : Type u}
    (M : X.Modules) (U : I → X.Opens) (hU : IsOpenCover U) (W : X.Opens) :
    Function.Injective ((toAffineCoverModule M U).val.app (op W)) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply TopCat.Presheaf.IsSheaf.section_ext
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M).cond
  intro x hx
  obtain ⟨i, hi⟩ := hU.exists_mem x
  refine ⟨W ⊓ U i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  change M.val.map (homOfLE inf_le_left).op s = M.val.map (homOfLE inf_le_left).op 0
  rw [map_zero]
  have hzero :
      ((SchemeModuleRestriction.restrictionAdjunction (U i).ι).unit.app M).val.app
        (op W) s = 0 := by
    rw [← toAffineCoverModule_comp_pi M U i]
    change (Pi.π (fun i => (SchemeModuleRestriction.restriction (U i).ι ⋙
      schemeModulePushforward (U i).ι).obj M) i).val.app (op W)
        ((toAffineCoverModule M U).val.app (op W) s) = 0
    rw [hs, map_zero]
  rw [restrictionUnit_app] at hzero
  have hle : W ⊓ U i ≤ (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inter, Scheme.Opens.opensRange_ι]
    exact le_inf inf_le_right inf_le_left
  have harrow : (homOfLE (image_preimage_le (U i).ι W)).op ≫ (homOfLE hle).op =
      (homOfLE (show W ⊓ U i ≤ W from inf_le_left)).op := Subsingleton.elim _ _
  calc
    M.val.map (homOfLE inf_le_left).op s =
        M.val.map ((homOfLE (image_preimage_le (U i).ι W)).op ≫ (homOfLE hle).op) s := by
      rw [harrow]
    _ = M.val.map (homOfLE hle).op
        (M.val.map (homOfLE (image_preimage_le (U i).ι W)).op s) := by
      exact ConcreteCategory.congr_hom (M.val.presheaf.map_comp _ _) s
    _ = 0 := by rw [hzero, map_zero]

/-- An actual open cover makes the cover map monic. -/
theorem toAffineCoverModule_mono {X : Scheme.{u}} {I : Type u}
    (M : X.Modules) (U : I → X.Opens) (hU : IsOpenCover U) :
    Mono (toAffineCoverModule M U) := by
  have hmono : Mono ((_root_.SheafOfModules.forget X.ringCatSheaf).map
      (toAffineCoverModule M U)) := by
    apply PresheafOfModules.mono_of_injective
    intro W
    exact toAffineCoverModule_app_injective M U hU W.unop
  exact Functor.mono_of_mono_map (_root_.SheafOfModules.forget X.ringCatSheaf) hmono

/-- The actual cover inclusion and its ambient cokernel form a short exact sequence. -/
theorem affineCoverCokernel_shortExact {X : Scheme.{u}} {I : Type u}
    (M : X.Modules) (U : I → X.Opens) (hU : IsOpenCover U) :
    (ShortComplex.mk (toAffineCoverModule M U) (cokernel.π (toAffineCoverModule M U))
      (cokernel.condition (toAffineCoverModule M U))).ShortExact := by
  letI := toAffineCoverModule_mono M U hU
  exact ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel (toAffineCoverModule M U))

end KltDP.Geometry.AffineCohomologyPort
