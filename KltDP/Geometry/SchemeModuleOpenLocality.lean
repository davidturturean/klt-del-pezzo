import KltDP.Geometry.ModuleRestrictionPullback
import KltDP.Compatibility.SheafIsoOnBasis
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Detecting actual scheme-module maps on an open cover

The existing image-open restriction identifies sections with the original
sections over image opens. The existing restriction/pullback comparison and
the existing sheaf basis criteria therefore detect equality and isomorphisms
of actual module maps on any actual covering family of scheme opens.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u v

namespace KltDP.Geometry

open SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original pullback along an open immersion preserves zero maps. -/
theorem schemeModulePullback_open_preservesZeroMorphisms
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    (schemeModulePullback f).PreservesZeroMorphisms := by
  letI : (restriction f).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact Functor.preservesZeroMorphisms_of_iso (restrictionIsoPullback f)

/-- The original open pullback preserves monomorphisms through its actual restriction comparison. -/
theorem schemeModulePullback_open_preservesMonomorphisms
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    (schemeModulePullback f).PreservesMonomorphisms := by
  letI : f.opensFunctor.IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    f.isOpenEmbedding.functor_isContinuous
  letI : (restriction f).IsRightAdjoint := by
    change (_root_.SheafOfModules.pushforward (restrictionRingSheafHom f)).IsRightAdjoint
    infer_instance
  exact Functor.preservesMonomorphisms.of_iso (restrictionIsoPullback f)

private theorem restriction_map_eq_of_pullback_map_eq
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {M N : X.Modules} {a b : M ⟶ N}
    (h : (schemeModulePullback f).map a = (schemeModulePullback f).map b) :
    (restriction f).map a = (restriction f).map b := by
  apply (cancel_mono ((restrictionIsoPullback f).hom.app N)).mp
  rw [(restrictionIsoPullback f).hom.naturality,
    (restrictionIsoPullback f).hom.naturality, h]

private theorem pullback_map_eq_app_of_le {X : Scheme.{u}}
    {M N : X.Modules} {a b : M ⟶ N} (U V : X.Opens) (hVU : V ≤ U)
    (h : (schemeModulePullback U.ι).map a = (schemeModulePullback U.ι).map b) :
    a.val.app (op V) = b.val.app (op V) := by
  have hr := restriction_map_eq_of_pullback_map_eq U.ι h
  have hi : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inter,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr hVU]
  have he : a.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) =
      b.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact congrArg (fun c : (restriction U.ι).obj M ⟶ (restriction U.ι).obj N =>
      c.val.app (op (U.ι ⁻¹ᵁ V)) s) hr
  rw [← hi]
  exact he

private theorem pullback_isIso_app_bijective_of_le {X : Scheme.{u}}
    {M N : X.Modules} (a : M ⟶ N) (U V : X.Opens) (hVU : V ≤ U)
    [IsIso ((schemeModulePullback U.ι).map a)] :
    Function.Bijective (a.val.app (op V)) := by
  letI : IsIso ((restriction U.ι).map a) :=
    (NatIso.isIso_map_iff (restrictionIsoPullback U.ι) a).mpr inferInstance
  have h : Function.Bijective (((restriction U.ι).map a).val.app (op (U.ι ⁻¹ᵁ V))) :=
    ConcreteCategory.bijective_of_isIso
      ((_root_.SheafOfModules.evaluation U.toScheme.ringCatSheaf
        (op (U.ι ⁻¹ᵁ V))).map ((restriction U.ι).map a))
  change Function.Bijective (a.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ V)))) at h
  have hi : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inter,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr hVU]
  rw [← hi]
  exact h

private theorem coverSubopens_isBasis {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i) :
    Opens.IsBasis (Set.range (fun p : ι × X.Opens => p.2 ⊓ U p.1)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro V x hx
  obtain ⟨i, hi⟩ := hU x
  exact ⟨V ⊓ U i, ⟨(i, V), rfl⟩, ⟨hx, hi⟩, inf_le_left⟩

/-- Equality of the original pullback maps on an actual open cover detects the original global map. -/
theorem schemeModule_hom_ext_of_openCover {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    {M N : X.Modules} (a b : M ⟶ N)
    (h : ∀ i, (schemeModulePullback (U i).ι).map a =
      (schemeModulePullback (U i).ι).map b) : a = b := by
  let B : ι × X.Opens → X.Opens := fun p => p.2 ⊓ U p.1
  have hB : Opens.IsBasis (Set.range B) := coverSubopens_isBasis U hU
  apply (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ hB
  intro p
  exact (forget₂ (ModuleCat (X.ringCatSheaf.val.obj (op (B p)))) AddCommGrp).congr_map
    (pullback_map_eq_app_of_le (U p.1) (B p) inf_le_right (h p.1))

/-- Isomorphisms of the original pullback maps on an actual open cover detect a global isomorphism. -/
theorem schemeModule_isIso_of_openCover {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    {M N : X.Modules} (a : M ⟶ N)
    (h : ∀ i, IsIso ((schemeModulePullback (U i).ι).map a)) : IsIso a := by
  let B : ι × X.Opens → X.Opens := fun p => p.2 ⊓ U p.1
  have hB : Opens.IsBasis (Set.range B) := coverSubopens_isBasis U hU
  apply KltDP.SheafOfModules.isIso_of_bijective_on_basis (B := B) a hB
  intro p
  letI := h p.1
  exact pullback_isIso_app_bijective_of_le a (U p.1) (B p) inf_le_right

end KltDP.Geometry
