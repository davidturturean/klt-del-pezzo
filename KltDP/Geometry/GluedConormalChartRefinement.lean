import KltDP.Geometry.GluedConormalBasicOpenLocalization
import KltDP.Geometry.SchemeKernelEquationRefinement
import KltDP.Geometry.SchemeConormalKernelPullback
import KltDP.Geometry.SchemeModulePullbackSquareFrames

/-!
# Refinement of the original global conormal chart frames

The actual quotient-chart frame is pullback of its original ambient-kernel
equation. The two ambient equations coincide after restriction by the proved
kernel-inclusion argument. The accepted pullback comparisons then transport
that equality through the original quotient-chart square.

The basic-open theorem derives the smaller principal regular equation from
the existing localization adapter. No agreement of frames or conormal
comparison is an input. Tilde-chart comparison and global adjunction descent
remain separate consumers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.GluedConormalChartRefinement

open SchemeModulePullbackSquareCoherence SchemeModulePullbackSquareFrames

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem inverse_component_word {A C D : Type*} [Category C] [Category D]
    (F : A → C ⥤ D) {a b : A} (h : a = b)
    {P Q : C ⥤ D} (p : P ≅ F b) (q : Q ≅ F a) (M : C) :
    (p ≪≫ eqToIso (congrArg F h.symm) ≪≫ q.symm).inv.app M =
      (q.app M ≪≫ (eqToIso (congrArg F h)).app M ≪≫ (p.app M).symm).hom := by
  subst b
  simp only [eqToIso_refl, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Iso.refl_inv, NatTrans.id_app, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
    Iso.refl_hom, Iso.symm_hom, Category.id_comp, Category.comp_id]

/-- Keep the two named maps in the conclusion before specializing their definitions. -/
private theorem inverse_component_named {A C D : Type*} [Category C] [Category D]
    (F : A → C ⥤ D) {a b : A} (h : a = b)
    {P Q : C ⥤ D} (p : P ≅ F b) (q : Q ≅ F a) (M : C)
    (r : P ≅ Q) (s : Q.obj M ≅ P.obj M)
    (hr : r = p ≪≫ eqToIso (congrArg F h.symm) ≪≫ q.symm)
    (hs : s = q.app M ≪≫ (eqToIso (congrArg F h)).app M ≪≫ (p.app M).symm) :
    r.inv.app M = s.hom := by
  rw [hr, hs]
  exact inverse_component_word F h p q M

-- Infer the exact equality from the two original named comparison maps.
-- This avoids checking the same concrete functor equality a second time.
set_option maxHeartbeats 800000 in
private def restriction_square_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (M : Y.Modules) :=
  inverse_component_named
    (fun k : (f ⁻¹ᵁ U).toScheme ⟶ Y => schemeModulePullback k)
    (morphismRestrict_ι f U)
    (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f)
    (schemeModulePullbackCompIso (f ∣_ U) U.ι) M
    (schemeModulePullbackRestrictIso f U)
    (squareIso f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U) (morphismRestrict_ι f U) M) rfl rfl

private theorem frame_refinement_congr {X V Y S T : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (j : S ⟶ X) (k : S ⟶ V)
    (h : k ≫ g = j ≫ f) (M : Y.Modules)
    (s : _root_.SheafOfModules.unit V.ringCatSheaf ⟶ (schemeModulePullback g).obj M)
    (q : T ⟶ S) {j' : T ⟶ X} {k' : T ⟶ V}
    (ej : q ≫ j = j') (ek : q ≫ k = k') (h' : k' ≫ g = j' ≫ f) :
    schemeModulePullbackFrame q
        (schemeModulePullbackFrame k s ≫ (squareIso f g j k h M).hom) ≫
      (schemeModulePullbackCompIso q j).hom.app ((schemeModulePullback f).obj M) ≫
      (eqToIso (congrArg schemeModulePullback ej)).hom.app
        ((schemeModulePullback f).obj M) =
      schemeModulePullbackFrame k' s ≫ (squareIso f g j' k' h' M).hom := by
  let hr := (Category.assoc q k g).trans
    ((congrArg (fun a => q ≫ a) h).trans (Category.assoc q j f).symm)
  calc
    _ = (schemeModulePullbackFrame (q ≫ k) s ≫
        (squareIso f g (q ≫ j) (q ≫ k) hr M).hom) ≫
        (eqToIso (congrArg schemeModulePullback ej)).hom.app
          ((schemeModulePullback f).obj M) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (eqToIso (congrArg schemeModulePullback ej)).hom.app
          ((schemeModulePullback f).obj M)) (frame_refinement f g j k h M s q)
    _ = _ := frame_congr f g (q ≫ j) (q ≫ k) hr M s ej ek h'

/-- Compose refinement of the two original square maps before inserting quotient charts. -/
private theorem frame_square_refinement {X V V' Y S T : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (g' : V' ⟶ Y)
    (j : S ⟶ X) (k : S ⟶ V) (j' : T ⟶ X) (k' : T ⟶ V')
    (h : k ≫ g = j ≫ f) (h' : k' ≫ g' = j' ≫ f) (M : Y.Modules)
    (a : V' ⟶ V) (b : T ⟶ S)
    (ea : a ≫ g = g') (ej : b ≫ j = j') (ek : b ≫ k = k' ≫ a)
    (s : _root_.SheafOfModules.unit V.ringCatSheaf ⟶ (schemeModulePullback g).obj M)
    (s' : _root_.SheafOfModules.unit V'.ringCatSheaf ⟶ (schemeModulePullback g').obj M)
    (r : _root_.SheafOfModules.unit S.ringCatSheaf ⟶
      (schemeModulePullback j).obj ((schemeModulePullback f).obj M))
    (r' : _root_.SheafOfModules.unit T.ringCatSheaf ⟶
      (schemeModulePullback j').obj ((schemeModulePullback f).obj M))
    (hs : schemeModulePullbackFrame a s ≫ (schemeModulePullbackCompIso a g).hom.app M ≫
      (eqToIso (congrArg schemeModulePullback ea)).hom.app M = s')
    (hr : r = schemeModulePullbackFrame k s ≫ (squareIso f g j k h M).hom)
    (hr' : r' = schemeModulePullbackFrame k' s' ≫ (squareIso f g' j' k' h' M).hom) :
    schemeModulePullbackFrame b r ≫
      (schemeModulePullbackCompIso b j).hom.app ((schemeModulePullback f).obj M) ≫
      (eqToIso (congrArg schemeModulePullback ej)).hom.app
        ((schemeModulePullback f).obj M) = r' := by
  rw [hr, hr']
  let hc : (k' ≫ a) ≫ g = j' ≫ f :=
    (Category.assoc k' a g).trans ((congrArg (fun z => k' ≫ z) ea).trans h')
  calc
    _ = schemeModulePullbackFrame (k' ≫ a) s ≫
        (squareIso f g j' (k' ≫ a) hc M).hom :=
      frame_refinement_congr f g j k h M s b ej ek hc
    _ = _ := by
      have hh := frame_ambient_refinement f g j' M s a g' ea k' h'
      rw [hs] at hh
      exact hh.symm

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The original global chart frame is the original kernel equation pulled through
its literal quotient-chart square. -/
theorem chartFrame_square (U : X.affineOpens) (d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :
    @Eq (_root_.SheafOfModules.unit (I.glueDataObj U).ringCatSheaf ⟶
        (schemeModulePullback (I.glueData.ι U)).obj (schemeConormalSheaf I.gluedTo))
      (gluedAffineConormalChartFrameIso I U d hU hd).hom
      (schemeModulePullbackFrame (I.glueDataObjι U)
        (localKernelGlobalEquation I.gluedTo U.1 (gluedAffineEquation U d)
          (gluedAffineEquation_eq_zero I U d hU)) ≫
        (squareIso I.gluedTo U.1.ι (I.glueData.ι U) (I.glueDataObjι U)
          (I.ι_gluedTo U).symm (schemeKernelIdeal I.gluedTo)).hom) := by
  have h := SchemeConormalKernelPullback.chartFrame I U d hU hd
  rw [restriction_square_hom] at h
  exact h.trans (frame_refinement_congr I.gluedTo U.1.ι (I.gluedTo ⁻¹ᵁ U.1).ι
    (I.gluedTo ∣_ U.1) (morphismRestrict_ι I.gluedTo U.1) (schemeKernelIdeal I.gluedTo)
    (localKernelGlobalEquation I.gluedTo U.1 (gluedAffineEquation U d)
      (gluedAffineEquation_eq_zero I U d hU)) (I.glueDataObjIso U).hom
    (I.glueDataObjIso_hom_ι U) (I.glueDataObjIso_hom_restrict U) (I.ι_gluedTo U).symm)

/-- A typed name for the original frame homomorphism, with its original target. -/
private def chartFrameHom (U : X.affineOpens) (d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :
    _root_.SheafOfModules.unit (I.glueDataObj U).ringCatSheaf ⟶
      (schemeModulePullback (I.glueData.ι U)).obj (schemeConormalSheaf I.gluedTo) :=
  (gluedAffineConormalChartFrameIso I U d hU hd).hom

/-- The original three restriction maps, with their common target checked once. -/
private def restrictedChartFrameHom (U V : X.affineOpens) (h : V ≤ U)
    (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
    (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :
    _root_.SheafOfModules.unit (I.glueDataObj V).ringCatSheaf ⟶
      (schemeModulePullback (I.glueData.ι V)).obj (schemeConormalSheaf I.gluedTo) :=
  schemeModulePullbackFrame (I.glueDataObjMap h) (chartFrameHom I U d hU hd) ≫
    (schemeModulePullbackCompIso (I.glueDataObjMap h) (I.glueData.ι U)).hom.app
      (schemeConormalSheaf I.gluedTo) ≫
    (eqToIso (congrArg schemeModulePullback (I.glueDataObjMap_ι V U h))).hom.app
      (schemeConormalSheaf I.gluedTo)

/-- Check the original one-chart kernel equation in its fixed module type once. -/
private def chartKernelEquation {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d}) :
    _root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf ⟶
      (schemeModulePullback U.1.ι).obj (schemeKernelIdeal I.gluedTo) :=
  localKernelGlobalEquation I.gluedTo U.1 (gluedAffineEquation U d)
    (gluedAffineEquation_eq_zero I U d hU)

/-- Name the original restricted section through the original ring homomorphism. -/
private def restrictedSection {X : Scheme.{u}} (U V : X.affineOpens)
    (h : V ≤ U) (d : Γ(X, U.1)) : Γ(X, V.1) :=
  (X.presheaf.map (homOfLE h).op).hom d

/-- Check the restricted original equation independently of the square application. -/
private def refinedChartKernelEquation (U V : X.affineOpens) (h : V ≤ U)
    (d : Γ(X, U.1))
    (hV : I.ideal V = Ideal.span {X.presheaf.map (homOfLE h).op d}) :
    _root_.SheafOfModules.unit V.1.toScheme.ringCatSheaf ⟶
      (schemeModulePullback V.1.ι).obj (schemeKernelIdeal I.gluedTo) := by
  let e : Γ(X, V.1) := restrictedSection U V h d
  change I.ideal V = Ideal.span {e} at hV
  exact chartKernelEquation I V e hV

/-- Check the restricted original frame in its fixed global conormal module. -/
private def refinedChartFrameHom (U V : X.affineOpens) (h : V ≤ U)
    (d : Γ(X, U.1))
    (hV : I.ideal V = Ideal.span {X.presheaf.map (homOfLE h).op d})
    (hdV : X.presheaf.map (homOfLE h).op d ∈ nonZeroDivisors Γ(X, V.1)) :
    _root_.SheafOfModules.unit (I.glueDataObj V).ringCatSheaf ⟶
      (schemeModulePullback (I.glueData.ι V)).obj (schemeConormalSheaf I.gluedTo) := by
  let e : Γ(X, V.1) := restrictedSection U V h d
  change I.ideal V = Ideal.span {e} at hV
  change e ∈ nonZeroDivisors Γ(X, V.1) at hdV
  exact chartFrameHom I V e hV hdV

/-- Infer the original smaller-chart square before the refinement proof uses it. -/
private def refinedChartFrame_square {X : Scheme.{u}} (I : X.IdealSheafData)
    (U V : X.affineOpens) (h : V ≤ U) (d : Γ(X, U.1))
    (hV : I.ideal V = Ideal.span {X.presheaf.map (homOfLE h).op d})
    (hdV : X.presheaf.map (homOfLE h).op d ∈ nonZeroDivisors Γ(X, V.1)) :=
  let e : Γ(X, V.1) := restrictedSection U V h d
  let hVe : I.ideal V = Ideal.span {e} := hV
  let hdVe : e ∈ nonZeroDivisors Γ(X, V.1) := hdV
  chartFrame_square I V e hVe hdVe

/-- Specialize the fixed original quotient-chart square before supplying any
local equations or frames. All six schemes are explicit at this boundary. -/
private def quotientChart_square_refinement {X : Scheme.{u}} (I : X.IdealSheafData)
    (U V : X.affineOpens) (h : V ≤ U) :=
  frame_square_refinement
    (X := I.glueData.glued) (Y := X) (V := U.1.toScheme) (V' := V.1.toScheme)
    (S := I.glueDataObj U) (T := I.glueDataObj V)
    I.gluedTo U.1.ι V.1.ι
    (I.glueData.ι U) (I.glueDataObjι U) (I.glueData.ι V) (I.glueDataObjι V)
    (I.ι_gluedTo U).symm (I.ι_gluedTo V).symm (schemeKernelIdeal I.gluedTo)
    (X.homOfLE h) (I.glueDataObjMap h)
    (X.homOfLE_ι h) (I.glueDataObjMap_ι V U h) (I.glueDataObjMap_glueDataObjι h)

set_option maxHeartbeats 800000 in
private def chartFrame_refinement_proof {X : Scheme.{u}} (I : X.IdealSheafData)
    (U V : X.affineOpens) (h : V ≤ U)
    (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
    (hdU : d ∈ nonZeroDivisors Γ(X, U.1))
    (hV : I.ideal V = Ideal.span {X.presheaf.map (homOfLE h).op d})
    (hdV : X.presheaf.map (homOfLE h).op d ∈ nonZeroDivisors Γ(X, V.1)) :=
  quotientChart_square_refinement I U V h
    (chartKernelEquation I U d hU)
    (refinedChartKernelEquation I U V h d hV)
    (chartFrameHom I U d hU hdU)
    (refinedChartFrameHom I U V h d hV hdV)
    (by simpa only [refinedChartKernelEquation, chartKernelEquation, kernelFrameRefinement,
      Category.assoc] using
      SchemeKernelEquationRefinement.affineEquation_refinement I U V h d hU)
    (chartFrame_square I U d hU hdU)
    (refinedChartFrame_square I U V h d hV hdV)

/-- Restricting one original regular equation yields the same global conormal frame
through the actual inclusion between its quotient charts. Its inferred proposition
is the exact original map equality; `statementOf` is transparent. -/
theorem chartFrame_refinement (U V : X.affineOpens) (h : V ≤ U)
    (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
    (hdU : d ∈ nonZeroDivisors Γ(X, U.1))
    (hV : I.ideal V = Ideal.span {X.presheaf.map (homOfLE h).op d})
    (hdV : X.presheaf.map (homOfLE h).op d ∈ nonZeroDivisors Γ(X, V.1)) :
    statementOf (chartFrame_refinement_proof I U V h d hU hdU hV hdV) :=
  chartFrame_refinement_proof I U V h d hU hdU hV hdV

/-- On an actual basic open the smaller regular equation is produced by localization,
so the original global conormal frame square needs no additional chart hypotheses. -/
theorem chartFrame_basicOpen (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :
    schemeModulePullbackFrame (I.glueDataObjMap (X.affineBasicOpen_le r))
        (gluedAffineConormalChartFrameIso I U d hU hd).hom ≫
      (schemeModulePullbackCompIso (I.glueDataObjMap (X.affineBasicOpen_le r))
        (I.glueData.ι U)).hom.app (schemeConormalSheaf I.gluedTo) ≫
      (eqToIso (congrArg schemeModulePullback
        (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r)))).hom.app
        (schemeConormalSheaf I.gluedTo) =
      (gluedAffineConormalChartFrameIso I (X.affineBasicOpen r)
        (GluedConormalBasicOpenLocalization.sectionMap U r d)
        (GluedConormalBasicOpenLocalization.equation_span I U r d hU)
        (GluedConormalBasicOpenLocalization.equation_regular U r d hd)).hom :=
  chartFrame_refinement I U (X.affineBasicOpen r) (X.affineBasicOpen_le r) d hU hd
    (GluedConormalBasicOpenLocalization.equation_span I U r d hU)
    (GluedConormalBasicOpenLocalization.equation_regular U r d hd)

end KltDP.Geometry.GluedConormalChartRefinement
