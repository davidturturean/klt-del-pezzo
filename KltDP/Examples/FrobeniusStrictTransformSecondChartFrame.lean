import KltDP.Examples.FrobeniusStrictTransformSecondChart
import KltDP.Geometry.GluedIdealKernelTrivialization

/-!
# The normalized original strict-kernel frame on the second Rees open

The actual second residual equation is regular: evaluation on the original
old coordinate curve sends it to one. Its exact original ideal equality
therefore yields a frame of the original whole-stage kernel, with its
inclusion equal to multiplication by the transported original equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformSecondChartFrame

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusExceptionalSuccessorChart
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformSecondChartAlgebra FrobeniusStrictTransformSecondChart

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The original old-coordinate evaluation sends the residual equation to one, including `m=0`. -/
theorem oldCurveMap_secondResidualEquation (m : ℕ) :
    oldCurveMap (secondResidualEquation (k := k) m) = 1 := by
  rw [secondResidualEquation, map_sub, map_one, map_mul, oldCurveMap_oldRatio,
    mul_zero, sub_zero]

theorem secondResidualEquation_ne_zero (m : ℕ) :
    secondResidualEquation (k := k) m ≠ 0 := by
  intro h
  have h' := congrArg (oldCurveMap (k := k)) h
  rw [oldCurveMap_secondResidualEquation, map_zero] at h'
  exact one_ne_zero h'

/-- Regularity follows through the already proved polynomial presentation of the actual chart. -/
theorem secondResidualEquation_regular (m : ℕ) :
    secondResidualEquation (k := k) m ∈ nonZeroDivisors (reesVChartRing k) := by
  apply mem_nonZeroDivisors_of_injective (f := vChartPolynomialEquiv (k := k))
    (vChartPolynomialEquiv (k := k)).injective
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  apply secondResidualEquation_ne_zero (k := k) m
  exact (vChartPolynomialEquiv (k := k)).injective
    (h.trans (map_zero (vChartPolynomialEquiv (k := k))).symm)

/-- The original second Rees chart as an affine open of the entire stage. -/
def secondAffineOpen (n : ℕ) : (projectiveContactStage (k := k) (n + 1)).affineOpens :=
  ⟨secondStageChart n ''ᵁ ⊤,
    (isAffineOpen_top (Spec (CommRingCat.of (reesVChartRing k)))).image_of_isOpenImmersion _⟩

/-- Both original section-ring isomorphisms, in their actual order. -/
def secondSectionsEquiv (n : ℕ) : reesVChartRing k ≃+*
    Γ(projectiveContactStage (k := k) (n + 1), (secondAffineOpen n).1) :=
  (Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).symm.commRingCatIsoToRingEquiv.trans
    ((secondStageChart n).appIso ⊤).symm.commRingCatIsoToRingEquiv

/-- The actual second residual equation in the original ambient section ring. -/
def secondAmbientEquation (n m : ℕ) :
    Γ(projectiveContactStage (k := k) (n + 1), (secondAffineOpen n).1) :=
  secondSectionsEquiv n (secondResidualEquation m)

/-- The principal ideal is the literal original whole-stage strict-transform ideal. -/
theorem strictIdeal_secondAffineOpen (n m : ℕ) :
    (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal (secondAffineOpen n) =
      Ideal.span {secondAmbientEquation n m} := by
  let e := secondSectionsEquiv (k := k) n
  have h : ((strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal
      (secondAffineOpen n)).comap e.toRingHom = Ideal.span {secondResidualEquation m} := by
    change strictSecondChartIdeal n m = _
    exact strictSecondChartIdeal_eq_span n m
  change (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal (secondAffineOpen n) =
    Ideal.span {e (secondResidualEquation m)}
  calc
    _ = (((strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal
        (secondAffineOpen n)).comap e.toRingHom).map e.toRingHom :=
      (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm
    _ = (Ideal.span {secondResidualEquation m}).map e.toRingHom := by rw [h]
    _ = _ := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl

theorem secondAmbientEquation_regular (n m : ℕ) :
    secondAmbientEquation (k := k) n m ∈
      nonZeroDivisors Γ(projectiveContactStage (k := k) (n + 1), (secondAffineOpen n).1) := by
  let e := secondSectionsEquiv (k := k) n
  apply mem_nonZeroDivisors_of_injective (f := e.symm) e.symm.injective
  change e.symm (e (secondResidualEquation m)) ∈ nonZeroDivisors (reesVChartRing k)
  simpa only [e.symm_apply_apply] using secondResidualEquation_regular (k := k) m

/-- The same equation in the actual affine open scheme's own global section ring. -/
def secondOpenEquation (n m : ℕ) : Γ((secondAffineOpen (k := k) n).1.toScheme, ⊤) :=
  gluedAffineEquation (secondAffineOpen n) (secondAmbientEquation n m)

/-- The frame belongs to the literal pullback of the original global strict kernel. -/
def strictKernelSecondOpenFrame (n m : ℕ) :
    _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        (schemeKernelIdeal (strictTransformι (n + 1) (m + (n + 1)))) :=
  gluedAffineKernelIso (strictTransformIdeal (n + 1) (m + (n + 1))) (secondAffineOpen n)
      (secondAmbientEquation n m) (strictIdeal_secondAffineOpen n m)
      (secondAmbientEquation_regular n m) ≪≫
    localKernelToGlobalPullbackIso (strictTransformι (n + 1) (m + (n + 1)))
      (secondAffineOpen n).1

/-- The original inclusion of this original kernel frame multiplies by exactly the residual equation. -/
theorem strictKernelSecondOpenFrame_inclusion (n m : ℕ) :
    (strictKernelSecondOpenFrame (k := k) n m).hom ≫
        pulledKernelInclusion (strictTransformι (n + 1) (m + (n + 1)))
          (secondAffineOpen n).1.ι =
      (schemeScalarEnd (Y := (secondAffineOpen (k := k) n).1.toScheme)
          (secondOpenEquation n m) :
        _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf) := by
  simp only [strictKernelSecondOpenFrame, Iso.trans_hom, Category.assoc,
    localKernelToGlobalPullbackIso_inclusion, gluedAffineKernelIso_hom,
    schemeKernelGenerator_comp_ι, secondOpenEquation]

end KltDP.Examples.FrobeniusStrictTransformSecondChartFrame
