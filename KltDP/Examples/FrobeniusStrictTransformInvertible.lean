import KltDP.Examples.FrobeniusStrictTransformStageCover
import KltDP.Examples.FrobeniusStrictTransformPunctureKernel
import KltDP.Examples.FrobeniusGraphPicardClassAffine
import KltDP.Geometry.GluedIdealKernelTrivialization
import KltDP.Geometry.QuasicoherentOpenPresentation

/-!
# Invertibility of the original whole-stage strict-transform kernel

The original strict ideal's proved chart restriction has the regular
equation `v-u^m`, through the actual chart section-ring isomorphism.
The existing quotient-chart kernel frame therefore frames the original
global kernel on that ambient open, with its inclusion normalized.

The actual strict-curve complement already has its unit kernel frame.
On the original stage puncture the original kernel is already proved
invertible. Its actual Over-site trivializations are converted to
scheme-open frames through the existing equivalence and composed actual
pullbacks. The proved three-open cover then gives invertibility on the
entire original stage using the existing local-frame criterion.

The field and natural stage/residual exponents are the only inputs.
No total-transform factorization or divisor-class identity is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformInvertible

open KltDP.Geometry SchemeModuleRestriction
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusStrictTransformClosure FrobeniusGlobalStrictTransform
open FrobeniusGraphPicardClassAffine FrobeniusStrictTransformStageCover
open FrobeniusStrictTransformPunctureKernel
open FrobeniusStageComplement.PlaneChartedScheme

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The actual current plane chart, regarded as an affine open of the whole stage. -/
def firstAffineOpen (n : ℕ) : (projectiveContactStage (k := k) n).affineOpens :=
  ⟨((projectiveProductInitial (k := k)).stage n).chart ''ᵁ ⊤,
    (isAffineOpen_top (plane k)).image_of_isOpenImmersion _⟩

/-- The residual equation transported by the original chart's section-ring isomorphism. -/
def firstAmbientEquation (n m : ℕ) :
    Γ(projectiveContactStage (k := k) n, (firstAffineOpen n).1) :=
  (((projectiveProductInitial (k := k)).stage n).chart.appIso ⊤).inv
    (firstEquation m)

/-- This is the original global strict ideal, with its actual chart coordinates retained. -/
theorem strictIdeal_firstAffineOpen (n m : ℕ) :
    (strictTransformIdeal (k := k) n (m + n)).ideal (firstAffineOpen n) =
      Ideal.span {firstAmbientEquation n m} := by
  let e := (((projectiveProductInitial (k := k)).stage n).chart.appIso ⊤).symm.commRingCatIsoToRingEquiv
  have h : Ideal.span {firstEquation (k := k) m} =
      ((strictTransformIdeal (k := k) n (m + n)).ideal
        (firstAffineOpen n)).comap e.toRingHom := by
    rw [strictTransformIdeal_eq_local]
    have hc := liftedGraphClosureIdeal_chart (projectiveProductInitial (k := k))
      n m ⟨⊤, isAffineOpen_top (plane k)⟩
    rw [Scheme.Hom.ker_apply, firstEquation_kernel] at hc
    exact hc
  change (strictTransformIdeal (k := k) n (m + n)).ideal (firstAffineOpen n) =
    Ideal.span {e (firstEquation m)}
  calc
    _ = (((strictTransformIdeal (k := k) n (m + n)).ideal
        (firstAffineOpen n)).comap e.toRingHom).map e.toRingHom :=
      (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm
    _ = (Ideal.span {firstEquation m}).map e.toRingHom := by rw [← h]
    _ = _ := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl

/-- Its regularity follows from the original monic residual equation. -/
theorem firstAmbientEquation_regular (n m : ℕ) :
    firstAmbientEquation (k := k) n m ∈
      nonZeroDivisors Γ(projectiveContactStage (k := k) n, (firstAffineOpen n).1) := by
  let e := (((projectiveProductInitial (k := k)).stage n).chart.appIso ⊤).symm.commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := e.symm) e.symm.injective
  change e.symm (e (firstEquation m)) ∈
    nonZeroDivisors Γ(plane k, ⊤)
  simpa only [e.symm_apply_apply] using firstEquation_regular (k := k) m

/-- The same equation in the actual affine open's own global section ring. -/
def firstOpenEquation (n m : ℕ) : Γ((firstAffineOpen (k := k) n).1.toScheme, ⊤) :=
  gluedAffineEquation (firstAffineOpen n) (firstAmbientEquation n m)

/-- The frame belongs to the literal pullback of the original whole strict kernel. -/
def strictKernelFirstOpenFrame (n m : ℕ) :
    _root_.SheafOfModules.unit (firstAffineOpen (k := k) n).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (firstAffineOpen (k := k) n).1.ι).obj
        (schemeKernelIdeal (strictTransformι n (m + n))) :=
  gluedAffineKernelIso (strictTransformIdeal n (m + n)) (firstAffineOpen n)
      (firstAmbientEquation n m) (strictIdeal_firstAffineOpen n m)
      (firstAmbientEquation_regular n m) ≪≫
    localKernelToGlobalPullbackIso (strictTransformι n (m + n)) (firstAffineOpen n).1

/-- Its original ambient inclusion is multiplication by the original transported equation. -/
theorem strictKernelFirstOpenFrame_inclusion (n m : ℕ) :
    (strictKernelFirstOpenFrame (k := k) n m).hom ≫
        pulledKernelInclusion (strictTransformι n (m + n)) (firstAffineOpen n).1.ι =
      (schemeScalarEnd (Y := (firstAffineOpen (k := k) n).1.toScheme)
          (firstOpenEquation n m) :
        _root_.SheafOfModules.unit (firstAffineOpen (k := k) n).1.toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit (firstAffineOpen (k := k) n).1.toScheme.ringCatSheaf) := by
  simp only [strictKernelFirstOpenFrame, Iso.trans_hom, Category.assoc,
    localKernelToGlobalPullbackIso_inclusion, gluedAffineKernelIso_hom,
    schemeKernelGenerator_comp_ι, firstOpenEquation]

/-- Existing pullback comparisons turn an actual open-immersion frame into an ambient-open frame. -/
private def frameOnOpensRange {X Y : Scheme.{u}} (M : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j]
    (e : _root_.SheafOfModules.unit X.ringCatSheaf ≅ (schemeModulePullback j).obj M) :
    _root_.SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf ≅
      (restriction j.opensRange.ι).obj M :=
  (schemeModulePullbackUnitIso j.isoOpensRange.inv).symm ≪≫
    (schemeModulePullback j.isoOpensRange.inv).mapIso e ≪≫
    (schemeModulePullbackCompIso j.isoOpensRange.inv j).app M ≪≫
    (eqToIso (congrArg schemeModulePullback (Scheme.Hom.isoOpensRange_inv_comp j))).app M ≪≫
    ((restrictionIsoPullback j.opensRange.ι).app M).symm

/-- Puncture trivializations give actual ambient neighborhoods of each puncture point. -/
private theorem strictKernel_puncture_openFrame (n m : ℕ)
    (x : projectiveContactStage (k := k) n)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) n) :
    ∃ V : (projectiveContactStage (k := k) n).Opens, x ∈ V ∧
      Nonempty (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf ≅
        (restriction V.ι).obj (schemeKernelIdeal (strictTransformι n (m + n)))) := by
  let P := stagePuncture (projectiveProductInitial (k := k)) n
  let M := schemeKernelIdeal (strictTransformι (k := k) n (m + n))
  let L := (schemeModulePullback P.ι).obj M
  letI : KltDP.SheafOfModules.IsInvertible (R := P.toScheme.ringCatSheaf) L :=
    strictKernel_stagePuncture_isInvertible n m
  let t := KltDP.SheafOfModules.LocalTrivializations.ofIsInvertible
    (R := P.toScheme.ringCatSheaf) L
  let y : P.toScheme := ⟨x, hx⟩
  obtain ⟨W, f, ⟨a, ⟨g⟩⟩, hyW⟩ := t.coversTop (⊤ : P.toScheme.Opens) y trivial
  have hya : y ∈ t.X a := g.le hyW
  let V : P.toScheme.Opens := t.X a
  let eOver : _root_.SheafOfModules.unit (P.toScheme.ringCatSheaf.over V) ≅ L.over V :=
    (_root_.SheafOfModules.freeUniqueIsoUnit
      (R := P.toScheme.ringCatSheaf.over V) PUnit).symm ≪≫ t.iso a
  let eOpen : _root_.SheafOfModules.unit V.toScheme.ringCatSheaf ≅
      (restriction V.ι).obj L :=
    overToOpenUnitIso V ≪≫ (openToOverEquivalence V).inverse.mapIso eOver ≪≫
      overToOpenRestrictionIso V L
  let j : V.toScheme ⟶ projectiveContactStage (k := k) n := V.ι ≫ P.ι
  let e : _root_.SheafOfModules.unit V.toScheme.ringCatSheaf ≅
      (schemeModulePullback j).obj M :=
    eOpen ≪≫ (restrictionIsoPullback V.ι).app L ≪≫
      (schemeModulePullbackCompIso V.ι P.ι).app M
  refine ⟨j.opensRange, ?_, ⟨frameOnOpensRange M j e⟩⟩
  exact ⟨⟨y, hya⟩, rfl⟩

/-- The original strict-transform kernel is invertible on the entire original stage. -/
theorem strictKernel_isInvertible (n m : ℕ) :
    KltDP.SheafOfModules.IsInvertible (R := (projectiveContactStage (k := k) n).ringCatSheaf)
      (schemeKernelIdeal (strictTransformι n (m + n))) := by
  apply isInvertible_of_openCharts (X := projectiveContactStage (k := k) n)
    (schemeKernelIdeal (strictTransformι n (m + n)))
  intro x
  rcases strictStage_cover (k := k) n m x with hc | hs | hp
  · refine ⟨(firstAffineOpen n).1, ?_, ⟨strictKernelFirstOpenFrame n m ≪≫
      ((restrictionIsoPullback (firstAffineOpen n).1.ι).app _).symm⟩⟩
    simpa only [firstAffineOpen, Scheme.Hom.image_top_eq_opensRange] using hc
  · exact ⟨strictCurveComplement n m, hs, ⟨strictCurveComplementFrame n m ≪≫
      ((restrictionIsoPullback (strictCurveComplement n m).ι).app _).symm⟩⟩
  · exact strictKernel_puncture_openFrame n m x hp

/-- The resulting line has literally the original whole strict-transform kernel as its object. -/
def strictKernelLine (n m : ℕ) : InvertibleSheaf (projectiveContactStage (k := k) n) :=
  ⟨schemeKernelIdeal (strictTransformι n (m + n)), strictKernel_isInvertible n m⟩

@[simp] theorem strictKernelLine_obj (n m : ℕ) :
    (strictKernelLine (k := k) n m).obj =
      schemeKernelIdeal (strictTransformι n (m + n)) := rfl

end KltDP.Examples.FrobeniusStrictTransformInvertible
