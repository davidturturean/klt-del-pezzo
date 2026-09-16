import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusExceptionalNormal
import KltDP.Geometry.PointBlowupCenterFiber
import KltDP.Geometry.SchemeConormalSourceIso
import KltDP.Geometry.SchemeConormalOpenImmersion
import KltDP.Geometry.SchemeInvertibleDualPullback

/-!
# The original exceptional normal of a whole point-blowup stage

The actual center fiber of the whole glued blowup is identified with the
original quotient-glued exceptional scheme. Source-isomorphism and target-open
conormal comparisons retain the original closed embeddings. Pulling the proved
affine conormal line back along the inverse fiber isomorphism then proves that
the actual global conormal is locally free of rank one.

The normal is its original sheaf dual. Its pullback comparison with the affine
normal preserves the actual conormal comparison and the original evaluation.
No global rank-one, normal comparison, cohomology transport, or intersection
value is supplied as a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusGlobalExceptionalNormal

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section DualComparison

local instance globalNormalSectionsComm (S : Scheme.{u}) :
    ∀ U, IsMulCommutative (S.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (S.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance globalNormalModulesMonoidal (S : Scheme.{u}) : MonoidalCategory S.Modules :=
  Scheme.Modules.monoidalCategory S

local instance globalNormalModulesSymmetric (S : Scheme.{u}) : SymmetricCategory S.Modules :=
  Scheme.Modules.symmetricCategory S

private def lineTensorFullyFaithful {S : Scheme.{u}} (L : InvertibleSheaf S) :
    (tensorLeft L.obj).FullyFaithful := by
  let D := schemeDualSheaf L.obj
  let d : L.obj ⊗ D ≅ 𝟙_ S.Modules := schemeDualEvaluationIso L ≪≫
    (PresheafOfModules.sheafTensorUnitIso S.sheaf.val S.ringCatSheaf.cond).symm
  exact (CategoryTheory.Equivalence.mk (tensorLeft L.obj) (tensorLeft D)
    ((tensorLeftTensor D L.obj).symm ≪≫
      (tensoringLeft S.Modules).mapIso ((β_ D L.obj) ≪≫ d) ≪≫
      leftUnitorNatIso S.Modules).symm
    ((tensorLeftTensor L.obj D).symm ≪≫
      (tensoringLeft S.Modules).mapIso d ≪≫ leftUnitorNatIso S.Modules)).fullyFaithfulFunctor

/-- Transport the original dual across an actual line isomorphism by
its original evaluation. This is a small use of pinned tensor cancellation. -/
private def lineDualComparison {S : Scheme.{u}} (L N : InvertibleSheaf S)
    (c : L.obj ≅ N.obj) : schemeDualSheaf L.obj ≅ schemeDualSheaf N.obj :=
  (lineTensorFullyFaithful L).preimageIso
    (schemeDualEvaluationIso L ≪≫
      ((tensorRight (schemeDualSheaf N.obj)).mapIso c ≪≫ schemeDualEvaluationIso N).symm)

private theorem lineDualComparison_evaluation {S : Scheme.{u}} (L N : InvertibleSheaf S)
    (c : L.obj ≅ N.obj) :
    L.obj ◁ (lineDualComparison L N c).hom ≫
        c.hom ▷ schemeDualSheaf N.obj ≫ (schemeDualEvaluationIso N).hom =
      (schemeDualEvaluationIso L).hom := by
  let d := (tensorRight (schemeDualSheaf N.obj)).mapIso c ≪≫ schemeDualEvaluationIso N
  change (tensorLeft L.obj).map
    ((lineTensorFullyFaithful L).preimage (schemeDualEvaluationIso L ≪≫ d.symm).hom) ≫
      d.hom = (schemeDualEvaluationIso L).hom
  rw [(lineTensorFullyFaithful L).map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

local instance originIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The actual categorical fiber over the original closed center. -/
abbrev globalExceptionalScheme : Scheme.{u} :=
  PointBlowupGluing.globalCenterFiber A.chart (originPoint (k := k)) A.center_closed

/-- The original fiber inclusion into the whole glued point blowup. -/
abbrev globalExceptionalInclusion : globalExceptionalScheme A ⟶ A.nextScheme :=
  PointBlowupGluing.globalCenterFiberι A.chart (originPoint (k := k)) A.center_closed

instance globalExceptionalInclusion_isClosedImmersion :
    IsClosedImmersion (globalExceptionalInclusion A) :=
  PointBlowupGluing.globalCenterFiberι_isClosedImmersion
    A.chart (originPoint (k := k)) A.center_closed

/-- The derived actual affine-to-global exceptional fiber isomorphism. -/
def affineExceptionalIso :
    AffineBlowup.exceptionalScheme (centerIdeal (k := k)) ≅ globalExceptionalScheme A :=
  PointBlowupGluing.exceptionalGlobalFiberIso
    A.chart (originPoint (k := k)) A.center_closed

/-- This isomorphism preserves both original exceptional embeddings. -/
theorem affineExceptionalIso_hom_inclusion :
    (affineExceptionalIso A).hom ≫ globalExceptionalInclusion A =
      AffineBlowup.exceptionalι (centerIdeal (k := k)) ≫ A.nextAffineBlowup :=
  PointBlowupGluing.exceptionalGlobalFiberIso_hom_ι
    A.chart (originPoint (k := k)) A.center_closed

/-- Pullback of the actual global conormal is the actual affine conormal,
using the original fiber square and the original target open inclusion. -/
def globalConormalPullbackIso :
    (schemeModulePullback (affineExceptionalIso A).hom).obj
      (schemeConormalSheaf (globalExceptionalInclusion A)) ≅
        AffineBlowup.exceptionalConormalSheaf (centerIdeal (k := k)) :=
  schemeConormalSourceIso (affineExceptionalIso A) (globalExceptionalInclusion A) ≪≫
    eqToIso (congrArg (fun g : AffineBlowup.exceptionalScheme (centerIdeal (k := k)) ⟶
      A.nextScheme => schemeConormalSheaf g) (affineExceptionalIso_hom_inclusion A)) ≪≫
    schemeConormalPostcompOpenIso (AffineBlowup.exceptionalι (centerIdeal (k := k)))
      A.nextAffineBlowup

/-- Pull the affine conormal back along the inverse original fiber iso,
then cancel the actual inverse/hom composite using the original functors. -/
def affineConormalDescentIso :
    (schemeModulePullback (affineExceptionalIso A).inv).obj
      (AffineBlowup.exceptionalConormalSheaf (centerIdeal (k := k))) ≅
        schemeConormalSheaf (globalExceptionalInclusion A) :=
  (schemeModulePullback (affineExceptionalIso A).inv).mapIso (globalConormalPullbackIso A).symm ≪≫
    (schemeModulePullbackCompIso (affineExceptionalIso A).inv
      (affineExceptionalIso A).hom).app (schemeConormalSheaf (globalExceptionalInclusion A)) ≪≫
    (eqToIso (congrArg schemeModulePullback (affineExceptionalIso A).inv_hom_id)).app
      (schemeConormalSheaf (globalExceptionalInclusion A)) ≪≫
    (schemeModulePullbackIdIso (globalExceptionalScheme A)).app
      (schemeConormalSheaf (globalExceptionalInclusion A))

/-- Global rank one is derived from the proved actual affine conormal
line and inverse-fiber transport, with no global invertibility premise. -/
def globalConormalLine : InvertibleSheaf (globalExceptionalScheme A) :=
  InvertibleSheaf.ofIso
    (pullbackInvertibleSheaf (affineExceptionalIso A).inv
      (AffineBlowup.exceptionalConormalLine (centerIdeal (k := k))))
    (affineConormalDescentIso A)

theorem globalConormalLine_obj :
    (globalConormalLine A).obj = schemeConormalSheaf (globalExceptionalInclusion A) := rfl

theorem globalConormal_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (globalExceptionalScheme A).ringCatSheaf)
      (schemeConormalSheaf (globalExceptionalInclusion A)) :=
  (globalConormalLine A).property

/-- The normal is the dual of the original conormal on the literal whole
center fiber, equipped with its derived local rank-one property. -/
def globalNormalLine : InvertibleSheaf (globalExceptionalScheme A) :=
  dualInvertibleSheaf (globalConormalLine A)

theorem globalNormalLine_obj :
    (globalNormalLine A).obj = schemeNormalSheaf (globalExceptionalInclusion A) := rfl

/-- The original global normal pulls back to the original affine normal.
First use normalized dual/pullback, then the exact conormal isomorphism. -/
def globalNormalPullbackIso :
    (schemeModulePullback (affineExceptionalIso A).hom).obj
      (schemeNormalSheaf (globalExceptionalInclusion A)) ≅
        schemeNormalSheaf (AffineBlowup.exceptionalι (centerIdeal (k := k))) :=
  schemeModulePullbackDualIso (affineExceptionalIso A).hom (globalConormalLine A) ≪≫
    lineDualComparison
      (pullbackInvertibleSheaf (affineExceptionalIso A).hom (globalConormalLine A))
      (AffineBlowup.exceptionalConormalLine (centerIdeal (k := k)))
      (globalConormalPullbackIso A)

/-- Normal and conormal transport preserve the original pulled evaluation,
including the original pullback unit normalization. -/
theorem globalNormalPullbackIso_evaluation :
    (schemeModulePullback (affineExceptionalIso A).hom).obj
        (schemeConormalSheaf (globalExceptionalInclusion A)) ◁ (globalNormalPullbackIso A).hom ≫
      (globalConormalPullbackIso A).hom ▷
        schemeNormalSheaf (AffineBlowup.exceptionalι (centerIdeal (k := k))) ≫
      (schemeDualEvaluationIso (AffineBlowup.exceptionalConormalLine (centerIdeal (k := k)))).hom =
      (schemeModulePullbackDualEvaluationIso (affineExceptionalIso A).hom
        (globalConormalLine A)).hom := by
  simp only [globalNormalPullbackIso, Iso.trans_hom,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact (congrArg
    (fun t :
        (pullbackInvertibleSheaf (affineExceptionalIso A).hom (globalConormalLine A)).obj ⊗
          schemeDualSheaf
            (pullbackInvertibleSheaf (affineExceptionalIso A).hom (globalConormalLine A)).obj ⟶
          _root_.SheafOfModules.unit
            (AffineBlowup.exceptionalScheme (centerIdeal (k := k))).ringCatSheaf =>
      (schemeModulePullback (affineExceptionalIso A).hom).obj
          (schemeConormalSheaf (globalExceptionalInclusion A)) ◁
        (schemeModulePullbackDualIso (affineExceptionalIso A).hom
          (globalConormalLine A)).hom ≫ t)
    (lineDualComparison_evaluation
      (pullbackInvertibleSheaf (affineExceptionalIso A).hom (globalConormalLine A))
      (AffineBlowup.exceptionalConormalLine (centerIdeal (k := k)))
      (globalConormalPullbackIso A))).trans
    (schemeModulePullbackDualIso_evaluation (affineExceptionalIso A).hom (globalConormalLine A))

end DualComparison

end KltDP.Examples.FrobeniusGlobalExceptionalNormal
