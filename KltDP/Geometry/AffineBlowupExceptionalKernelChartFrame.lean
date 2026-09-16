import KltDP.Geometry.AffineBlowupAmbientFrameComparison

/-!
# The original exceptional kernel frame on each actual Rees chart

The proved original regular equation gives a frame of the actual global
exceptional ideal pulled to the original affine Rees chart. The original
kernel inclusion sends this frame to multiplication by that same equation,
through the original Gamma-Spec section comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineBlowup

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private def kernelRefinementIso {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (i : Z ⟶ Y) (g : W ⟶ Z) (j : W ⟶ Y) (h : g ≫ i = j)
    (e : _root_.SheafOfModules.unit Z.ringCatSheaf ≅
      (schemeModulePullback i).obj (schemeKernelIdeal f)) :
    _root_.SheafOfModules.unit W.ringCatSheaf ≅
      (schemeModulePullback j).obj (schemeKernelIdeal f) :=
  (schemeModulePullbackUnitIso g).symm ≪≫ (schemeModulePullback g).mapIso e ≪≫
    (schemeModulePullbackCompIso g i).app (schemeKernelIdeal f) ≪≫
      (eqToIso (congrArg schemeModulePullback h)).app (schemeKernelIdeal f)

private theorem kernelRefinementIso_hom {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (i : Z ⟶ Y) (g : W ⟶ Z) (j : W ⟶ Y) (h : g ≫ i = j)
    (e : _root_.SheafOfModules.unit Z.ringCatSheaf ≅
      (schemeModulePullback i).obj (schemeKernelIdeal f)) :
    (kernelRefinementIso f i g j h e).hom =
      kernelFrameRefinement f i g e.hom ≫
        (eqToIso (congrArg schemeModulePullback h)).hom.app (schemeKernelIdeal f) := by
  simp only [kernelRefinementIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, kernelFrameRefinement,
    schemeModulePullbackFrame, Category.assoc]

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)

/-- The existing regular equation frames the original kernel on its original range open. -/
def chartKernelGlobalIso :
    _root_.SheafOfModules.unit (chartAffineOpen I a).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (chartAffineOpen I a).1.ι).obj (exceptionalIdealModule I) :=
  gluedAffineKernelIso (exceptionalIdeal I) (chartAffineOpen I a)
      (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)
      (chartEquationSection_regular I a) ≪≫
    localKernelToGlobalPullbackIso (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1

theorem chartKernelGlobalIso_hom :
    (chartKernelGlobalIso I a).hom =
      localKernelGlobalEquation (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
        (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
        (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
          (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)) := rfl

/-- Transport this original equation frame to the actual affine Rees chart. -/
def originalChartKernelFrameIso :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (chartRing I a))).ringCatSheaf ≅
      (schemeModulePullback (chartι I a)).obj (exceptionalIdealModule I) :=
  kernelRefinementIso (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1.ι
    (chartAmbientIso I a).hom (chartι I a) (chartAmbientIso_hom_ι I a)
    (chartKernelGlobalIso I a)

/-- The chosen isomorphism is the original normalized equation refinement. -/
theorem originalChartKernelFrameIso_hom :
    (originalChartKernelFrameIso I a).hom =
      kernelFrameRefinement (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1.ι
        (chartAmbientIso I a).hom
        (localKernelGlobalEquation (exceptionalIdeal I).gluedTo (chartAffineOpen I a).1
          (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
          (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
            (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a))) ≫
        (eqToIso (congrArg schemeModulePullback (chartAmbientIso_hom_ι I a))).hom.app
          (schemeKernelIdeal (exceptionalIdeal I).gluedTo) := by
  rw [originalChartKernelFrameIso, kernelRefinementIso_hom, chartKernelGlobalIso_hom]

/-- The inclusion is multiplication by the original Rees equation on this same chart. -/
theorem originalChartKernelFrameIso_inclusion :
    (originalChartKernelFrameIso I a).hom ≫
        pulledKernelInclusion (exceptionalIdeal I).gluedTo (chartι I a) =
      schemeScalarEnd
        ((Scheme.ΓSpecIso (CommRingCat.of (chartRing I a))).inv
          (chartCenterEquation I a)) := by
  rw [originalChartKernelFrameIso_hom, Category.assoc,
    pulledKernelInclusion_congr (exceptionalIdeal I).gluedTo (chartAmbientIso_hom_ι I a),
    localKernelGlobalEquation_refinement_inclusion, chartAmbientIso_equation]

end KltDP.Geometry.AffineBlowup
