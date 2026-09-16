import KltDP.Geometry.SchemeConormalSourceIso
import KltDP.Geometry.SchemeConormalOpenImmersion
import KltDP.Geometry.AffineBlowupConormalChartFrames

/-!
# Original equation maps through source and ambient chart comparisons

The accepted conormal comparisons preserve the original equation maps.
At the kernel this follows by their existing ideal-inclusion formulas;
at the conormal it follows by the existing normalized frame composition.
These identities apply before any equation is known to be regular.

No frame agreement, comparison map, or transition equation is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

section Source

variable {X' X Y : Scheme.{u}} (e : X' ≅ X) (f : X ⟶ Y)
  (d : Γ(Y, ⊤)) (hd : f.appTop d = 0)

include hd in
/-- The original equation is still killed after the actual source isomorphism. -/
theorem schemeEquation_sourceIso_eq_zero : (e.hom ≫ f).appTop d = 0 := by
  change e.hom.appTop (f.appTop d) = 0
  rw [hd, e.hom.appTop.hom.map_zero]

/-- The original kernel comparison preserves the original equation lift. -/
theorem schemeKernelPrecompIso_generator :
    schemeKernelGenerator f d hd ≫ (schemeKernelPrecompIso e f).inv =
      schemeKernelGenerator (e.hom ≫ f) d (schemeEquation_sourceIso_eq_zero e f d hd) := by
  letI : Mono (schemeKernelIdealι (e.hom ≫ f)) := by
    unfold schemeKernelIdealι
    infer_instance
  apply (cancel_mono (schemeKernelIdealι (e.hom ≫ f))).mp
  rw [Category.assoc, schemeKernelPrecompIso_inv_ι,
    schemeKernelGenerator_comp_ι, schemeKernelGenerator_comp_ι]

/-- The actual source-isomorphism conormal comparison preserves the original pulled equation. -/
theorem schemeConormalSourceIso_generator :
    pulledConormalGenerator f e.hom d hd ≫ (schemeConormalSourceIso e f).hom =
      schemeConormalGenerator (e.hom ≫ f) d (schemeEquation_sourceIso_eq_zero e f d hd) := by
  change schemeModulePullbackFrame e.hom
      (schemeModulePullbackFrame f (schemeKernelGenerator f d hd)) ≫
      (schemeModulePullbackCompIso e.hom f).hom.app (schemeKernelIdeal f) ≫
        (schemeModulePullback (e.hom ≫ f)).map (schemeKernelPrecompIso e f).inv = _
  rw [← Category.assoc, schemeModulePullbackFrame_comp,
    ← schemeModulePullbackFrame_postcomp, schemeKernelPrecompIso_generator]
  rfl

end Source

section Ambient

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ Z) [IsOpenImmersion a]
  (d : Γ(Z, ⊤)) (hd : (f ≫ a).appTop d = 0)

include hd in
/-- Restricting the original ambient equation gives the equation of the original morphism. -/
theorem schemeEquation_postcompOpen_eq_zero : f.appTop (a.appTop d) = 0 := hd

/-- The ambient-open kernel comparison retains the original equation after restriction. -/
theorem schemeKernelPostcompOpenIso_generator :
    schemeModulePullbackFrame a (schemeKernelGenerator (f ≫ a) d hd) ≫
        (schemeKernelPostcompOpenIso f a).hom =
      schemeKernelGenerator f (a.appTop d) (schemeEquation_postcompOpen_eq_zero f a d hd) := by
  letI : Mono (schemeKernelIdealι f) := by
    unfold schemeKernelIdealι
    infer_instance
  apply (cancel_mono (schemeKernelIdealι f)).mp
  rw [Category.assoc, schemeKernelPostcompOpenIso_hom_ι, schemeKernelGenerator_comp_ι]
  change (schemeModulePullbackUnitIso a).inv ≫
      (schemeModulePullback a).map (schemeKernelGenerator (f ≫ a) d hd) ≫
      (schemeModulePullback a).map (schemeKernelIdealι (f ≫ a)) ≫
        (schemeModulePullbackUnitIso a).hom = schemeScalarEnd (a.appTop d)
  rw [← Functor.map_comp_assoc, schemeKernelGenerator_comp_ι,
    ← Category.assoc, schemeModulePullbackUnitIso_inv_scalar,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The existing ambient-open conormal comparison preserves the original equation map. -/
theorem schemeConormalPostcompOpenIso_generator :
    schemeConormalGenerator (f ≫ a) d hd ≫ (schemeConormalPostcompOpenIso f a).hom =
      schemeConormalGenerator f (a.appTop d) (schemeEquation_postcompOpen_eq_zero f a d hd) := by
  change schemeModulePullbackFrame (f ≫ a) (schemeKernelGenerator (f ≫ a) d hd) ≫
      (schemeModulePullbackCompIso f a).inv.app (schemeKernelIdeal (f ≫ a)) ≫
        (schemeModulePullback f).map (schemeKernelPostcompOpenIso f a).hom = _
  rw [← schemeModulePullbackFrame_comp a f (schemeKernelGenerator (f ≫ a) d hd)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← schemeModulePullbackFrame_postcomp, schemeKernelPostcompOpenIso_generator]
  rfl

end Ambient

end KltDP.Geometry
