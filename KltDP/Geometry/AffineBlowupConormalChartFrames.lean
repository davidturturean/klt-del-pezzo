import KltDP.Geometry.AffineBlowupExceptionalChartComparison

/-!
# Original Rees equation frames on actual conormal pullbacks

The original quotient-chart comparison transports the constructed equation
frame to the pullback of the global exceptional conormal along the original
Rees chart map. Normalized pullback composition preserves the equation map,
including after an arbitrary further morphism into that chart.

No chart frame, frame agreement, or transition coefficient is assumed.
The two different ambient-chart comparisons on a common overlap still have
to be identified before extracting a global projective-line transition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable {X Y Z : Scheme.{u}}

/-- Pull an actual map out of the structure module back with the original
pullback-unit normalization. -/
def schemeModulePullbackFrame (g : Y ⟶ X) {M : X.Modules}
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ (schemeModulePullback g).obj M :=
  (schemeModulePullbackUnitIso g).inv ≫ (schemeModulePullback g).map s

/-- Actual frame transport commutes with postcomposition. -/
theorem schemeModulePullbackFrame_postcomp (g : Y ⟶ X) {M N : X.Modules}
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ M) (f : M ⟶ N) :
    schemeModulePullbackFrame g (s ≫ f) =
      schemeModulePullbackFrame g s ≫ (schemeModulePullback g).map f := by
  simp only [schemeModulePullbackFrame, Functor.map_comp, Category.assoc]

/-- The actual pullback-composition comparison preserves normalized frames. -/
theorem schemeModulePullbackFrame_comp (g : Y ⟶ X) (h : Z ⟶ Y) {M : X.Modules}
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    schemeModulePullbackFrame h (schemeModulePullbackFrame g s) ≫
        (schemeModulePullbackCompIso h g).hom.app M =
      schemeModulePullbackFrame (h ≫ g) s := by
  have hu := congrArg (fun q =>
    (schemeModulePullbackUnitIso h).inv ≫
      (schemeModulePullback h).map (schemeModulePullbackUnitIso g).inv ≫
        q ≫ (schemeModulePullbackUnitIso (h ≫ g)).inv)
    (schemeModulePullbackCompIso_unit h g)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc] at hu
  simp only [schemeModulePullbackFrame, Functor.map_comp, Category.assoc]
  have hn := (schemeModulePullbackCompIso h g).hom.naturality s
  simp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ (schemeModulePullback (h ≫ g)).map s) hu

/-- In particular, repeated actual pullback retains the original equation
map, not a newly chosen unit multiple of it. -/
theorem pulledConormalGenerator_comp {W : Scheme.{u}} (f : X ⟶ W)
    (g : Y ⟶ X) (h : Z ⟶ Y) (d : Γ(W, ⊤)) (hd : f.appTop d = 0) :
    schemeModulePullbackFrame h (pulledConormalGenerator f g d hd) ≫
        (schemeModulePullbackCompIso h g).hom.app (schemeConormalSheaf f) =
      pulledConormalGenerator f (h ≫ g) d hd :=
  schemeModulePullbackFrame_comp g h (schemeConormalGenerator f d hd)

namespace AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)

/-- The original exceptional Rees chart map into the actual glued exceptional
scheme, through the already constructed fiber comparison. -/
def originalExceptionalChartMap : exceptionalChart I a ⟶ exceptionalScheme I :=
  exceptionalChartToFiber I a ≫ (exceptionalFiberIso I).inv

/-- The same original chart maps to the actual restricted closed scheme
through its original quotient-chart isomorphism. -/
def originalExceptionalChartLocalMap : exceptionalChart I a ⟶
    ((exceptionalIdeal I).gluedTo ⁻¹ᵁ (chartAffineOpen I a).1).toScheme :=
  (exceptionalGluedChartIso I a).hom ≫
    ((exceptionalIdeal I).glueDataObjIso (chartAffineOpen I a)).hom

/-- Iterated pullback through the original quotient chart agrees with
pullback through its proved original exceptional-chart map. -/
def originalExceptionalChartPullbackIso :
    (schemeModulePullback (exceptionalGluedChartIso I a).hom).obj
      ((schemeModulePullback ((exceptionalIdeal I).glueData.ι
        (chartAffineOpen I a))).obj (schemeConormalSheaf (exceptionalIdeal I).gluedTo)) ≅
    (schemeModulePullback (originalExceptionalChartMap I a)).obj
      (schemeConormalSheaf (exceptionalIdeal I).gluedTo) :=
  (schemeModulePullbackCompIso (exceptionalGluedChartIso I a).hom
    ((exceptionalIdeal I).glueData.ι (chartAffineOpen I a))).app _ ≪≫
      (eqToIso (congrArg schemeModulePullback
        (exceptionalGluedChartIso_hom_toExceptional I a))).app _

/-- The original Rees equation defines an actual frame of the global
conormal pulled back along the original exceptional chart map. -/
def originalExceptionalChartFrameIso :
    _root_.SheafOfModules.unit (exceptionalChart I a).ringCatSheaf ≅
      (schemeModulePullback (originalExceptionalChartMap I a)).obj
        (schemeConormalSheaf (exceptionalIdeal I).gluedTo) :=
  (schemeModulePullbackUnitIso (exceptionalGluedChartIso I a).hom).symm ≪≫
    (schemeModulePullback (exceptionalGluedChartIso I a).hom).mapIso
      (gluedAffineConormalChartFrameIso (exceptionalIdeal I) (chartAffineOpen I a)
        (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)
        (chartEquationSection_regular I a)) ≪≫
      originalExceptionalChartPullbackIso I a

/-- Compare that actual global pullback with the original local conormal
pulled back along the same chart's actual local map. -/
def originalExceptionalChartConormalComparisonIso :
    (schemeModulePullback (originalExceptionalChartMap I a)).obj
      (schemeConormalSheaf (exceptionalIdeal I).gluedTo) ≅
    (schemeModulePullback (originalExceptionalChartLocalMap I a)).obj
      (schemeConormalSheaf ((exceptionalIdeal I).gluedTo ∣_ (chartAffineOpen I a).1)) :=
  (originalExceptionalChartPullbackIso I a).symm ≪≫
    (schemeModulePullback (exceptionalGluedChartIso I a).hom).mapIso
      (gluedAffineConormalChartComparisonIso (exceptionalIdeal I) (chartAffineOpen I a)) ≪≫
    (schemeModulePullbackCompIso (exceptionalGluedChartIso I a).hom
      ((exceptionalIdeal I).glueDataObjIso (chartAffineOpen I a)).hom).app _

/-- The original Rees chart frame is precisely its original pulled equation
map through the actual local comparison. No frame agreement is an input. -/
theorem originalExceptionalChartFrameIso_comparison :
    (originalExceptionalChartFrameIso I a).hom ≫
        (originalExceptionalChartConormalComparisonIso I a).hom =
      pulledConormalGenerator
        ((exceptionalIdeal I).gluedTo ∣_ (chartAffineOpen I a).1)
        (originalExceptionalChartLocalMap I a)
        (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
        (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
          (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)) := by
  simp only [originalExceptionalChartFrameIso,
    originalExceptionalChartConormalComparisonIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  change schemeModulePullbackFrame (exceptionalGluedChartIso I a).hom
      (gluedAffineConormalChartFrameIso (exceptionalIdeal I) (chartAffineOpen I a)
        (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)
        (chartEquationSection_regular I a)).hom ≫
    (schemeModulePullback (exceptionalGluedChartIso I a).hom).map
      (gluedAffineConormalChartComparisonIso (exceptionalIdeal I)
        (chartAffineOpen I a)).hom ≫
    (schemeModulePullbackCompIso (exceptionalGluedChartIso I a).hom
      ((exceptionalIdeal I).glueDataObjIso (chartAffineOpen I a)).hom).hom.app _ = _
  rw [← Category.assoc, ← schemeModulePullbackFrame_postcomp,
    gluedAffineConormalChartFrameIso_comparison]
  exact pulledConormalGenerator_comp _ _ _ _ _

/-- Arbitrary further pullback into the original chart preserves that
same original equation frame and the normalized composite map. -/
theorem originalExceptionalChartFrameIso_refinement {T : Scheme.{u}}
    (h : T ⟶ exceptionalChart I a) :
    schemeModulePullbackFrame h (originalExceptionalChartFrameIso I a).hom ≫
      (schemeModulePullback h).map (originalExceptionalChartConormalComparisonIso I a).hom ≫
        (schemeModulePullbackCompIso h (originalExceptionalChartLocalMap I a)).hom.app _ =
      pulledConormalGenerator
        ((exceptionalIdeal I).gluedTo ∣_ (chartAffineOpen I a).1)
        (h ≫ originalExceptionalChartLocalMap I a)
        (gluedAffineEquation (chartAffineOpen I a) (chartEquationSection I a))
        (gluedAffineEquation_eq_zero (exceptionalIdeal I) (chartAffineOpen I a)
          (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)) := by
  rw [← Category.assoc, ← schemeModulePullbackFrame_postcomp, originalExceptionalChartFrameIso_comparison]
  exact pulledConormalGenerator_comp _ _ _ _ _

end AffineBlowup

end KltDP.Geometry
