import KltDP.Geometry.SchemeKernelRestriction
import KltDP.Geometry.SchemeConormalEquationChange

/-!
# Actual kernel equation maps commute with restriction to scheme opens

The canonical kernel comparison for an open restriction carries the
actual equation map to the map of the restricted equation. The scalar
comparison is proved on the original section rings, and the kernel
comparison is characterized by its original inclusion.

This is the equation-level naturality needed before comparing conormal
charts. No agreement of frames or sheaf trivializations is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (U : Y.Opens)

/-- Restriction of the actual multiplication map is multiplication by
the original equation restricted through the open immersion. -/
theorem restriction_schemeScalarEnd (d : Γ(Y, ⊤)) :
    (SchemeModuleRestriction.restriction U.ι).map (schemeScalarEnd d) ≫
        (SchemeModuleRestriction.restrictionUnitIso U.ι).hom =
      (SchemeModuleRestriction.restrictionUnitIso U.ι).hom ≫
        schemeScalarEnd (U.ι.appTop d) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let s' : Γ(Y, U.ι ''ᵁ V.unop) := s
  change (U.ι.appIso V.unop).hom
      ((schemeScalarEnd d).val.app (op (U.ι ''ᵁ V.unop)) s) =
    (schemeScalarEnd (U.ι.appTop d)).val.app V ((U.ι.appIso V.unop).hom s)
  rw [Scheme.Opens.ι_appIso]
  simp only [schemeScalarEnd_app]
  change s' * Y.presheaf.map _ d = s' * Y.presheaf.map _ (Y.presheaf.map _ d)
  rw [← CommRingCat.comp_apply, ← Functor.map_comp] <;> rfl

variable (f : X ⟶ Y) (d : Γ(Y, ⊤)) (hd : f.appTop d = 0)

include hd in
/-- The restricted equation is killed by the actual restricted morphism. -/
theorem restrictedEquation_eq_zero : (f ∣_ U).appTop (U.ι.appTop d) = 0 := by
  have h := congrArg (fun g => g.appTop) (morphismRestrict_ι f U)
  simp only [Scheme.comp_appTop] at h
  have he := ConcreteCategory.congr_hom h d
  change (f ∣_ U).appTop (U.ι.appTop d) =
    (f ⁻¹ᵁ U).ι.appTop (f.appTop d) at he
  rw [hd, (f ⁻¹ᵁ U).ι.appTop.hom.map_zero] at he
  exact he

/-- The actual kernel comparison carries the original equation map to
the equation map of the actual open restriction. -/
theorem schemeKernelRestrictionIso_generator :
    (SchemeModuleRestriction.restriction U.ι).map (schemeKernelGenerator f d hd) ≫
        (schemeKernelRestrictionIso f U).hom =
      (SchemeModuleRestriction.restrictionUnitIso U.ι).hom ≫
        schemeKernelGenerator (f ∣_ U) (U.ι.appTop d)
          (restrictedEquation_eq_zero U f d hd) := by
  apply (cancel_mono (kernel.ι (structureToPushforwardUnit (f ∣_ U)))).mp
  change ((SchemeModuleRestriction.restriction U.ι).map (schemeKernelGenerator f d hd) ≫
      (schemeKernelRestrictionIso f U).hom) ≫ schemeKernelIdealι (f ∣_ U) =
    ((SchemeModuleRestriction.restrictionUnitIso U.ι).hom ≫
      schemeKernelGenerator (f ∣_ U) (U.ι.appTop d)
        (restrictedEquation_eq_zero U f d hd)) ≫ schemeKernelIdealι (f ∣_ U)
  rw [Category.assoc, schemeKernelRestrictionIso_hom_ι, ← Category.assoc,
    ← Functor.map_comp, schemeKernelGenerator_comp_ι, Category.assoc,
    schemeKernelGenerator_comp_ι]
  exact restriction_schemeScalarEnd U d

end KltDP.Geometry
