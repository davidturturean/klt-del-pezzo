import KltDP.Examples.FrobeniusTowerTransport
import KltDP.Geometry.SchematicImageToImageIso
import KltDP.Geometry.GluedIdealSheafKernel
import KltDP.Examples.FrobeniusFiberClosure
import KltDP.Examples.FrobeniusStrictTransformClosure
import KltDP.Geometry.RationalTreePicardDualGraphTransport

/-!
# The curves of the towers correspond under the stage isomorphisms

Kernel-ideal transport along an isomorphism of the target: for quasi-compact `f, f' : W ⟶ Y` with
`f.ker = f'.ker` and an isomorphism `g : Y ⟶ Z`, `(f ≫ g).ker = (f' ≫ g).ker` (`ker_comp_iso_congr`,
componentwise from the pinned `Hom.ker_apply`); hence, for a square `f ≫ g = φ ≫ f'` with `φ` an
isomorphism, the schematic closure `f.ker.gluedTo` of `f` composed with `g` has the kernel of `f'`
(`closure_ker_eq`), and the closures are isomorphic over `g` when both are reduced
(`closureIso`, BRIEF14's `isoOfKerEq`). Applied to an isomorphism of charted planes
`e : ChartedIso A B` and its stage isomorphisms (BRIEF23): the strict fibres `F̃_n`
(`fiberClosureIso`) and the strict transforms of the local graphs `v = u^m` (`graphClosureIso`)
of `A.stage n` are carried onto those of `B.stage n`, since the punctured lifts defining them are
built from the selected charts, which correspond (`stage_chart_comm`). For the translation
`projectiveProductInitial ≅ translatedInitial p a` this identifies the strict fibre and the graph
strict transform of the origin tower with those of the translated tower at every stage
(`fiberClosureTranslationIso`, `graphClosureTranslationIso`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerTransportCurves

open KltDP.Geometry KltDP.Geometry.SchematicImageToImageIso FrobeniusGlobalBlowupStages
  FrobeniusBlowupChartIteration FrobeniusBlowupContact FrobeniusTranslatedCharts
  FrobeniusContactTowerSelectedPoint FrobeniusTowerTransport FrobeniusFiberClosure
  FrobeniusStrictTransformClosure

variable {k : Type u} [Field k]

/-! ## Kernel ideal sheaves along isomorphisms -/

/-- Precomposition with an isomorphism does not change the kernel. -/
theorem ker_comp_of_isIso {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (f : Y ⟶ Z) :
    (e ≫ f).ker = f.ker := by
  apply le_antisymm
  · have h := Scheme.Hom.le_ker_comp (inv e) (e ≫ f)
    rwa [IsIso.inv_hom_id_assoc] at h
  · exact Scheme.Hom.le_ker_comp e f

/-- Postcomposition with an isomorphism: the kernel after `g` depends only on the kernel before. -/
theorem ker_comp_iso_congr {W W' Y Z : Scheme.{u}} (f : W ⟶ Y) (f' : W' ⟶ Y) [QuasiCompact f]
    [QuasiCompact f'] (g : Y ⟶ Z) [IsIso g] (h : f.ker = f'.ker) : (f ≫ g).ker = (f' ≫ g).ker := by
  unfold Scheme.Hom.ker
  apply congrArg Scheme.IdealSheafData.ofIdeals
  funext V
  rw [Scheme.comp_app, Scheme.comp_app, CommRingCat.hom_comp, CommRingCat.hom_comp,
    ← RingHom.comap_ker, ← RingHom.comap_ker]
  have hV : IsAffineOpen (g ⁻¹ᵁ V.1) := V.2.preimage_of_isIso g
  have h1 : RingHom.ker (f.app (g ⁻¹ᵁ V.1)).hom = f.ker.ideal ⟨g ⁻¹ᵁ V.1, hV⟩ :=
    (Scheme.Hom.ker_apply f ⟨g ⁻¹ᵁ V.1, hV⟩).symm
  have h2 : RingHom.ker (f'.app (g ⁻¹ᵁ V.1)).hom = f'.ker.ideal ⟨g ⁻¹ᵁ V.1, hV⟩ :=
    (Scheme.Hom.ker_apply f' ⟨g ⁻¹ᵁ V.1, hV⟩).symm
  rw [h1, h2, h]

/-- A square `f ≫ g = φ ≫ f'` with `g`, `φ` isomorphisms: the schematic closure of `f`, followed
by `g`, has the kernel of `f'`. -/
theorem closure_ker_eq {W W' Y Z : Scheme.{u}} (f : W ⟶ Y) (f' : W' ⟶ Z) [QuasiCompact f]
    [QuasiCompact f'] (g : Y ⟶ Z) [IsIso g] (φ : W ⟶ W') [IsIso φ] (sq : f ≫ g = φ ≫ f') :
    (f.ker.gluedTo ≫ g).ker = f'.ker := by
  rw [ker_comp_iso_congr f.ker.gluedTo f g f.ker.ker_gluedTo, sq, ker_comp_of_isIso]

/-- **Transport of schematic closures along an isomorphism.** -/
def closureIso {W W' Y Z : Scheme.{u}} (f : W ⟶ Y) (f' : W' ⟶ Z) [QuasiCompact f]
    [QuasiCompact f'] (g : Y ⟶ Z) [IsIso g] (φ : W ⟶ W') [IsIso φ] (sq : f ≫ g = φ ≫ f')
    [IsReduced f.ker.glueData.glued] [IsReduced f'.ker.glueData.glued] :
    f.ker.glueData.glued ≅ f'.ker.glueData.glued :=
  isoOfKerEq (f.ker.gluedTo ≫ g) f'.ker.gluedTo
    ((closure_ker_eq f f' g φ sq).trans f'.ker.ker_gluedTo.symm)

@[reassoc] theorem closureIso_hom {W W' Y Z : Scheme.{u}} (f : W ⟶ Y) (f' : W' ⟶ Z)
    [QuasiCompact f] [QuasiCompact f'] (g : Y ⟶ Z) [IsIso g] (φ : W ⟶ W') [IsIso φ]
    (sq : f ≫ g = φ ≫ f') [IsReduced f.ker.glueData.glued] [IsReduced f'.ker.glueData.glued] :
    (closureIso f f' g φ sq).hom ≫ f'.ker.gluedTo = f.ker.gluedTo ≫ g :=
  isoOfKerEq_hom _ _ _

end KltDP.Examples.FrobeniusTowerTransportCurves

namespace KltDP.Examples.FrobeniusTowerTransport.ChartedIso

open KltDP.Geometry KltDP.Geometry.SchematicImageToImageIso FrobeniusGlobalBlowupStages
  FrobeniusBlowupChartIteration FrobeniusBlowupContact FrobeniusFiberClosure
  FrobeniusStrictTransformClosure KltDP.Examples.FrobeniusTowerTransportCurves

variable {k : Type u} [Field k]

/-! ## The punctured parameter line is Noetherian -/

/-- The punctured affine line is a Noetherian space (open in `Spec k[t]`). -/
local instance parameterPuncture_noetherianSpace' :
    NoetherianSpace (parameterPuncture (k := k)).toScheme :=
  haveI : NoetherianSpace (Spec (CommRingCat.of (Polynomial k))) :=
    inferInstanceAs (NoetherianSpace (PrimeSpectrum (Polynomial k)))
  (parameterPuncture (k := k)).ι.isOpenEmbedding.isInducing.noetherianSpace

local instance puncturedFiberResidual_quasiCompact (A : PlaneChartedScheme k) (n : ℕ) :
    QuasiCompact (puncturedFiberResidual A n) :=
  quasiCompact_of_noetherianSpace_source _

local instance puncturedResidualCurve_quasiCompact (A : PlaneChartedScheme k) (n m : ℕ) :
    QuasiCompact (puncturedResidualCurve A n m) :=
  quasiCompact_of_noetherianSpace_source _

variable {A B : PlaneChartedScheme k} (e : ChartedIso A B)

/-! ## The strict fibres -/

/-- The punctured strict fibres correspond (they are built from the selected charts). -/
theorem puncturedFiberResidual_comm (n : ℕ) :
    puncturedFiberResidual A n ≫ (e.stage n).iso.hom =
      𝟙 _ ≫ puncturedFiberResidual B n := by
  rw [Category.id_comp, puncturedFiberResidual, puncturedFiberResidual, fiberResidual, fiberResidual,
    Category.assoc, Category.assoc, e.stage_chart_comm]

/-- **The strict fibre `F̃_n` of `A.stage n` is carried onto that of `B.stage n`.** -/
def fiberClosureIso (n : ℕ) : liftedFiberClosure A n ≅ liftedFiberClosure B n :=
  haveI hA : IsReduced (puncturedFiberResidual A n).ker.glueData.glued :=
    liftedFiberClosure_isReduced A n
  haveI hB : IsReduced (puncturedFiberResidual B n).ker.glueData.glued :=
    liftedFiberClosure_isReduced B n
  closureIso (puncturedFiberResidual A n) (puncturedFiberResidual B n) (e.stage n).iso.hom (𝟙 _)
    (e.puncturedFiberResidual_comm n)

@[reassoc] theorem fiberClosureIso_hom (n : ℕ) :
    (e.fiberClosureIso n).hom ≫ fiberClosureInclusion B n =
      fiberClosureInclusion A n ≫ (e.stage n).iso.hom := by
  haveI hA : IsReduced (puncturedFiberResidual A n).ker.glueData.glued :=
    liftedFiberClosure_isReduced A n
  haveI hB : IsReduced (puncturedFiberResidual B n).ker.glueData.glued :=
    liftedFiberClosure_isReduced B n
  exact closureIso_hom (puncturedFiberResidual A n) (puncturedFiberResidual B n)
    (e.stage n).iso.hom (𝟙 _) (e.puncturedFiberResidual_comm n)

/-! ## The strict transforms of the local graphs -/

/-- The punctured residual curves correspond. -/
theorem puncturedResidualCurve_comm (n m : ℕ) :
    puncturedResidualCurve A n m ≫ (e.stage n).iso.hom =
      𝟙 _ ≫ puncturedResidualCurve B n m := by
  rw [Category.id_comp, puncturedResidualCurve, puncturedResidualCurve,
    PlaneChartedScheme.residualCurve, PlaneChartedScheme.residualCurve, Category.assoc,
    Category.assoc, e.stage_chart_comm]

/-- **The strict transform of the local graph `v = u^m` of `A.stage n` is carried onto that of
`B.stage n`.** -/
def graphClosureIso (n m : ℕ) : liftedGraphClosure A n m ≅ liftedGraphClosure B n m :=
  haveI hA : IsReduced (puncturedResidualCurve A n m).ker.glueData.glued :=
    liftedGraphClosure_isReduced A n m
  haveI hB : IsReduced (puncturedResidualCurve B n m).ker.glueData.glued :=
    liftedGraphClosure_isReduced B n m
  closureIso (puncturedResidualCurve A n m) (puncturedResidualCurve B n m) (e.stage n).iso.hom
    (𝟙 _) (e.puncturedResidualCurve_comm n m)

@[reassoc] theorem graphClosureIso_hom (n m : ℕ) :
    (e.graphClosureIso n m).hom ≫ closureInclusion B n m =
      closureInclusion A n m ≫ (e.stage n).iso.hom := by
  haveI hA : IsReduced (puncturedResidualCurve A n m).ker.glueData.glued :=
    liftedGraphClosure_isReduced A n m
  haveI hB : IsReduced (puncturedResidualCurve B n m).ker.glueData.glued :=
    liftedGraphClosure_isReduced B n m
  exact closureIso_hom (puncturedResidualCurve A n m) (puncturedResidualCurve B n m)
    (e.stage n).iso.hom (𝟙 _) (e.puncturedResidualCurve_comm n m)

end KltDP.Examples.FrobeniusTowerTransport.ChartedIso

namespace KltDP.Examples.FrobeniusTowerTransportCurves

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts
  FrobeniusContactTowerSelectedPoint FrobeniusTowerTransport FrobeniusFiberClosure
  FrobeniusStrictTransformClosure

variable {k : Type u} [Field k]

/-! ## The translated towers -/

/-- **The strict fibre of the origin tower is carried onto the strict fibre of the translated
tower at every stage.** -/
def fiberClosureTranslationIso (p : ℕ) (a : k) (n : ℕ) :
    liftedFiberClosure (projectiveProductInitial (k := k)) n ≅
      liftedFiberClosure (translatedInitial p a) n :=
  (translationChartedIso p a).fiberClosureIso n

theorem fiberClosureTranslationIso_hom (p : ℕ) (a : k) (n : ℕ) :
    (fiberClosureTranslationIso p a n).hom ≫ fiberClosureInclusion (translatedInitial p a) n =
      fiberClosureInclusion (projectiveProductInitial (k := k)) n ≫
        (stageTranslationIso p a n).hom :=
  (translationChartedIso p a).fiberClosureIso_hom n

/-- **The strict transform of the local graph `v = u^m` of the origin tower is carried onto that of
the translated tower at every stage.** -/
def graphClosureTranslationIso (p : ℕ) (a : k) (n m : ℕ) :
    liftedGraphClosure (projectiveProductInitial (k := k)) n m ≅
      liftedGraphClosure (translatedInitial p a) n m :=
  (translationChartedIso p a).graphClosureIso n m

theorem graphClosureTranslationIso_hom (p : ℕ) (a : k) (n m : ℕ) :
    (graphClosureTranslationIso p a n m).hom ≫ closureInclusion (translatedInitial p a) n m =
      closureInclusion (projectiveProductInitial (k := k)) n m ≫ (stageTranslationIso p a n).hom :=
  (translationChartedIso p a).graphClosureIso_hom n m

end KltDP.Examples.FrobeniusTowerTransportCurves

namespace KltDP.Examples.FrobeniusTowerTransport.ChartedIso

open KltDP.Geometry KltDP.Geometry.PointBlowupGluing FrobeniusGlobalBlowupStages
  FrobeniusBlowupChartIteration FrobeniusGlobalExceptionalSuccessor
  FrobeniusExceptionalFinalConfiguration KltDP.Examples.FrobeniusTowerTransportCurves

variable {k : Type u} [Field k]

/-- The centre of a chart is a maximal ideal (the accepted witness). -/
local instance towerTransportCurvesOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## The older exceptional curves: the birth stage -/

/-- The punctured previous exceptional fibre is Noetherian (a closed subscheme of `P¹`, then an
open). -/
theorem previousPuncture_noetherianSpace' (C : PlaneChartedScheme k) :
    NoetherianSpace (previousPuncture C).toScheme :=
  haveI hP : NoetherianSpace (projectiveSpace k 1) := projectiveSpace_noetherianSpace k 1
  haveI hF : NoetherianSpace (previousFiber C) :=
    KltDP.Geometry.RationalTreePicard.noetherianSpace_of_isClosedImmersion
      (FrobeniusGlobalExceptionalSuccessor.previousFiberIso C).hom
  (previousPuncture C).ι.isOpenEmbedding.isInducing.noetherianSpace

local instance wholePreviousLift_quasiCompact' (C : PlaneChartedScheme k) :
    QuasiCompact (wholePreviousLift C) :=
  haveI := previousPuncture_noetherianSpace' C
  quasiCompact_of_noetherianSpace_source _

variable {A B : PlaneChartedScheme k} (e : ChartedIso A B)

/-- The punctured previous fibres correspond under `previousFiberMap`. -/
theorem range_previousPuncture_le :
    Set.range ((previousPuncture A).ι ≫ e.previousFiberMap).base ⊆
      Set.range (previousPuncture B).ι.base := by
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨e.previousFiberMap.base x.1, ?_⟩, rfl⟩
  have hx : (previousFiberι A).base x.1 ∉
      ({A.next.chart.base (originPoint (k := k))} : Set A.next.carrier) := x.2
  have h1 : (previousFiberι B).base (e.previousFiberMap.base x.1) =
      e.nextHom.base ((previousFiberι A).base x.1) :=
    congrArg (fun f => f.base x.1) e.previousFiberMap_ι
  change (previousFiberι B).base (e.previousFiberMap.base x.1) ∉
    ({B.next.chart.base (originPoint (k := k))} : Set B.next.carrier)
  rw [h1]
  intro h
  apply hx
  rw [Set.mem_singleton_iff] at h ⊢
  rw [← e.next.center_comm] at h
  exact e.nextHom.isOpenEmbedding.injective h

/-- The restriction of `previousFiberMap` to the punctured fibres. -/
def previousPunctureMap : (previousPuncture A).toScheme ⟶ (previousPuncture B).toScheme :=
  IsOpenImmersion.lift (previousPuncture B).ι ((previousPuncture A).ι ≫ e.previousFiberMap)
    e.range_previousPuncture_le

@[reassoc] theorem previousPunctureMap_ι :
    e.previousPunctureMap ≫ (previousPuncture B).ι =
      (previousPuncture A).ι ≫ e.previousFiberMap :=
  IsOpenImmersion.lift_fac _ _ _

theorem previousPunctureMap_symm : e.previousPunctureMap ≫ e.symm.previousPunctureMap = 𝟙 _ := by
  apply (cancel_mono (previousPuncture A).ι).mp
  rw [Category.assoc, previousPunctureMap_ι, ← Category.assoc, previousPunctureMap_ι,
    Category.assoc, previousFiberMap_symm, Category.comp_id, Category.id_comp]

theorem symm_previousPunctureMap : e.symm.previousPunctureMap ≫ e.previousPunctureMap = 𝟙 _ := by
  apply (cancel_mono (previousPuncture B).ι).mp
  rw [Category.assoc, previousPunctureMap_ι, ← Category.assoc, previousPunctureMap_ι,
    Category.assoc, symm_previousFiberMap, Category.comp_id, Category.id_comp]

instance previousPunctureMap_isIso : IsIso e.previousPunctureMap :=
  ⟨e.symm.previousPunctureMap, e.previousPunctureMap_symm, e.symm_previousPunctureMap⟩

/-- **The whole lifts of the punctured previous fibres correspond.** -/
theorem wholePreviousLift_comm :
    wholePreviousLift A ≫ e.next.nextHom = e.previousPunctureMap ≫ wholePreviousLift B := by
  have hL : wholePreviousLift A ≫ e.next.nextHom =
      ((previousFiberι A ∣_ puncture A.next.chart (originPoint (k := k)) A.next.center_closed) ≫
        e.next.punctureMap) ≫
          complementι B.next.chart (originPoint (k := k)) B.next.center_closed := by
    rw [wholePreviousLift, Category.assoc, e.next.complementι_nextHom, Category.assoc]
  have hR : e.previousPunctureMap ≫ wholePreviousLift B =
      (e.previousPunctureMap ≫
        (previousFiberι B ∣_ puncture B.next.chart (originPoint (k := k)) B.next.center_closed)) ≫
          complementι B.next.chart (originPoint (k := k)) B.next.center_closed := by
    rw [wholePreviousLift, Category.assoc]
  rw [hL, hR]
  congr 1
  apply (cancel_mono (puncture B.next.chart (originPoint (k := k)) B.next.center_closed).ι).mp
  have h1 : ((previousFiberι A ∣_ puncture A.next.chart (originPoint (k := k)) A.next.center_closed) ≫
      e.next.punctureMap) ≫
        (puncture B.next.chart (originPoint (k := k)) B.next.center_closed).ι =
      (previousPuncture A).ι ≫ previousFiberι A ≫ e.nextHom := by
    rw [Category.assoc, e.next.punctureMap_ι, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    rfl
  have h2 : (e.previousPunctureMap ≫
      (previousFiberι B ∣_ puncture B.next.chart (originPoint (k := k)) B.next.center_closed)) ≫
        (puncture B.next.chart (originPoint (k := k)) B.next.center_closed).ι =
      (previousPuncture A).ι ≫ previousFiberι A ≫ e.nextHom := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
    change (e.previousPunctureMap ≫ (previousPuncture B).ι) ≫ previousFiberι B = _
    rw [previousPunctureMap_ι, Category.assoc, previousFiberMap_ι]
  rw [h1, h2]

/-- **The strict transform `C` of the previous exceptional curve of `A.next` is carried onto that
of `B.next`.** -/
def previousStrictIso : previousStrictTransform A ≅ previousStrictTransform B :=
  haveI hA : IsReduced (wholePreviousLift A).ker.glueData.glued :=
    previousStrictTransform_isReduced A
  haveI hB : IsReduced (wholePreviousLift B).ker.glueData.glued :=
    previousStrictTransform_isReduced B
  closureIso (wholePreviousLift A) (wholePreviousLift B) e.next.nextHom e.previousPunctureMap
    e.wholePreviousLift_comm

@[reassoc] theorem previousStrictIso_hom :
    e.previousStrictIso.hom ≫ previousStrictι B = previousStrictι A ≫ e.next.nextHom := by
  haveI hA : IsReduced (wholePreviousLift A).ker.glueData.glued :=
    previousStrictTransform_isReduced A
  haveI hB : IsReduced (wholePreviousLift B).ker.glueData.glued :=
    previousStrictTransform_isReduced B
  exact closureIso_hom (wholePreviousLift A) (wholePreviousLift B) e.next.nextHom
    e.previousPunctureMap e.wholePreviousLift_comm

/-! ## The older exceptional curves on every later stage -/

/-- **`C_j` embedded in stage `N` of `A` is carried onto `C_j` embedded in stage `N` of `B`**
(the pullback squares `finalOldMap_isPullback` and `stage_hom_between`). -/
theorem finalOldMap_comm (N j : ℕ) (h : j + 2 ≤ N) :
    (e.stage j).previousStrictIso.hom ≫ finalOldMap B N j h =
      finalOldMap A N j h ≫ (e.stage N).iso.hom := by
  have hw : (finalOldMap A N j h ≫ (e.stage N).iso.hom) ≫ between B h =
      (e.stage j).previousStrictIso.hom ≫ previousStrictι (B.stage j) := by
    rw [Category.assoc, e.stage_hom_between h, ← Category.assoc, finalOldMap_projection,
      (e.stage j).previousStrictIso_hom]
    rfl
  have hl := (finalOldMap_isPullback B N j h).lift_fst _ _ hw
  have hl' := (finalOldMap_isPullback B N j h).lift_snd _ _ hw
  rw [Category.comp_id] at hl'
  rw [← hl', hl]

/-- The isomorphism of the indexed final components. -/
def finalComponentIso (n : ℕ) :
    (idx : FinalIndex n) → finalComponent A n idx ≅ finalComponent B n idx
  | .inl j => (e.stage j.val).previousStrictIso
  | .inr _ => (e.stage n).previousFiberIso

/-- **Every final exceptional component of `A.stage (n+1)` is carried onto the corresponding
component of `B.stage (n+1)`.** -/
theorem finalComponentIso_hom (n : ℕ) (idx : FinalIndex n) :
    (e.finalComponentIso n idx).hom ≫ finalComponentι B n idx =
      finalComponentι A n idx ≫ (e.stage (n + 1)).iso.hom := by
  cases idx with
  | inl j => exact e.finalOldMap_comm (n + 1) j.val (by omega)
  | inr t => exact (e.stage n).previousFiberMap_ι

/-- The supports of the final components correspond. -/
theorem finalSupport_eq (n : ℕ) (idx : FinalIndex n) :
    finalSupport B n idx = (e.stage (n + 1)).iso.hom.base '' finalSupport A n idx := by
  have h : finalComponentι B n idx =
      (e.finalComponentIso n idx).inv ≫ finalComponentι A n idx ≫ (e.stage (n + 1)).iso.hom := by
    rw [← e.finalComponentIso_hom, Iso.inv_hom_id_assoc]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(finalComponentι A n idx).base ((e.finalComponentIso n idx).inv.base x), ⟨_, rfl⟩, ?_⟩
    exact (congrArg (fun f => f.base x) h).symm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨(e.finalComponentIso n idx).hom.base x, ?_⟩
    have hx := congrArg (fun f => f.base x) (e.finalComponentIso_hom n idx)
    exact hx

end KltDP.Examples.FrobeniusTowerTransport.ChartedIso

namespace KltDP.Examples.FrobeniusTowerTransportCurves

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts
  FrobeniusContactTowerSelectedPoint FrobeniusTowerTransport FrobeniusGlobalExceptionalSuccessor
  FrobeniusExceptionalFinalConfiguration

variable {k : Type u} [Field k]

/-! ## The translated towers: the exceptional curves -/

/-- **`C_j` of the origin tower is carried onto `C_j` of the translated tower at every stage.** -/
theorem finalOldMap_translation (p : ℕ) (a : k) (N j : ℕ) (h : j + 2 ≤ N) :
    ((translationChartedIso p a).stage j).previousStrictIso.hom ≫
        finalOldMap (translatedInitial p a) N j h =
      finalOldMap (projectiveProductInitial (k := k)) N j h ≫ (stageTranslationIso p a N).hom :=
  (translationChartedIso p a).finalOldMap_comm N j h

/-- **Every final exceptional component of the origin tower is carried onto the corresponding
component of the translated tower**, and the supports correspond. -/
theorem finalComponentι_translation (p : ℕ) (a : k) (n : ℕ) (idx : FinalIndex n) :
    ((translationChartedIso p a).finalComponentIso n idx).hom ≫
        finalComponentι (translatedInitial p a) n idx =
      finalComponentι (projectiveProductInitial (k := k)) n idx ≫
        (stageTranslationIso p a (n + 1)).hom :=
  (translationChartedIso p a).finalComponentIso_hom n idx

theorem finalSupport_translation (p : ℕ) (a : k) (n : ℕ) (idx : FinalIndex n) :
    finalSupport (translatedInitial p a) n idx =
      (stageTranslationIso p a (n + 1)).hom.base ''
        finalSupport (projectiveProductInitial (k := k)) n idx :=
  (translationChartedIso p a).finalSupport_eq n idx

end KltDP.Examples.FrobeniusTowerTransportCurves
