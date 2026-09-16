import KltDP.Examples.FrobeniusStrictTransformAffineBlowup
import KltDP.Geometry.SchematicImageOpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The original one-step morphism between the whole strict transforms

The actual successor strict inclusion followed by the actual blowdown
has exactly the previous strict ideal as its schematic-image kernel.
This is computed on the already proved nonempty open residual chart of
the integral successor strict curve, using the original Rees projection.

The existing quotient-image factorization therefore constructs the
actual morphism to the previous whole strict curve and preserves both
original inclusions. Its composite with the previous inclusion is proper;
hence its actual image is closed and it is surjective. No strict-curve
projection, image equality, or surjectivity is an input hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStrictTransformStepProjection

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusStrictTransformClosure FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformContact FrobeniusStrictTransformAffineBlowup

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The two original residual curves agree after the original one-step blowdown. -/
@[reassoc] theorem residualCurve_stepProjection (n m : ℕ) :
    (projectiveProductInitial (k := k)).residualCurve (n + 1) m ≫
        (projectiveProductInitial (k := k)).stepProjection n =
      (projectiveProductInitial (k := k)).residualCurve n (m + 1) := by
  rw [PlaneChartedScheme.residualCurve_succ, Category.assoc]
  change residualCurveMorphism m ≫
      (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup ≫
        ((projectiveProductInitial (k := k)).stage n).nextProjection) = _
  rw [PlaneChartedScheme.nextAffineBlowup_projection, ← Category.assoc,
    residualCurveMorphism_toSpec]
  rfl

/-- The actual projected successor strict curve has the original previous strict ideal. -/
theorem strictStep_composite_ker (n m : ℕ) :
    (strictTransformι (k := k) (n + 1) (m + (n + 1)) ≫
      (projectiveProductInitial (k := k)).stepProjection n).ker =
        strictTransformIdeal n ((m + 1) + n) := by
  letI : IsIntegral (strictTransform (k := k) (n + 1) (m + (n + 1))) :=
    strictTransform_isIntegral (n + 1) m
  rw [← SchematicImageOpenImmersion.ker_precompose_openImmersion
    (residualChart (k := k) (n + 1) m)
    (strictTransformι (n + 1) (m + (n + 1)) ≫
      (projectiveProductInitial (k := k)).stepProjection n)]
  rw [← Category.assoc, residualChart_ι, residualCurve_stepProjection,
    strictTransformIdeal_eq_local n (m + 1), liftedGraphClosureIdeal_eq]

private theorem gluedTo_eqToIso_hom {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : I = J) :
    (eqToIso (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h)).hom ≫
      J.gluedTo = I.gluedTo := by
  subst J
  exact Category.id_comp _

/-- The proved original image-ideal equality identifies the actual quotient-glued targets. -/
def strictStepImageIso (n m : ℕ) :
    SchematicImageGlued.image
      (strictTransformι (k := k) (n + 1) (m + (n + 1)) ≫
        (projectiveProductInitial (k := k)).stepProjection n) ≅
      strictTransform (k := k) n ((m + 1) + n) :=
  eqToIso (congrArg
    (fun I : (projectiveContactStage (k := k) n).IdealSheafData => I.glueData.glued)
    (strictStep_composite_ker n m))

/-- The actual one-step projection between the original entire strict curves. -/
def strictStepProjection (n m : ℕ) :
    strictTransform (k := k) (n + 1) (m + (n + 1)) ⟶
      strictTransform (k := k) n ((m + 1) + n) :=
  SchematicImageGlued.toImage
      (strictTransformι (n + 1) (m + (n + 1)) ≫
        (projectiveProductInitial (k := k)).stepProjection n) ≫
    (strictStepImageIso n m).hom

/-- The constructed map preserves the original inclusions and original blowdown. -/
@[reassoc] theorem strictStepProjection_inclusion (n m : ℕ) :
    strictStepProjection (k := k) n m ≫ strictTransformι n ((m + 1) + n) =
      strictTransformι (n + 1) (m + (n + 1)) ≫
        (projectiveProductInitial (k := k)).stepProjection n := by
  rw [strictStepProjection, Category.assoc]
  change SchematicImageGlued.toImage _ ≫
    ((strictStepImageIso n m).hom ≫ (strictTransformIdeal n ((m + 1) + n)).gluedTo) = _
  rw [strictStepImageIso, gluedTo_eqToIso_hom (strictStep_composite_ker n m)]
  exact SchematicImageGlued.toImage_inclusion _

/-- Its actual composite image is closed because the original ambient blowdown is proper. -/
theorem strictStep_composite_range (n m : ℕ) :
    Set.range (strictTransformι (k := k) n ((m + 1) + n)).base =
      Set.range (strictTransformι (n + 1) (m + (n + 1)) ≫
        (projectiveProductInitial (k := k)).stepProjection n).base := by
  let g := strictTransformι (k := k) (n + 1) (m + (n + 1)) ≫
    (projectiveProductInitial (k := k)).stepProjection n
  letI : IsProper g := inferInstance
  change Set.range (strictTransformIdeal n ((m + 1) + n)).gluedTo.base = Set.range g.base
  rw [Scheme.IdealSheafData.range_gluedTo, ← strictStep_composite_ker (k := k) n m]
  change (g.ker.support : Set (projectiveContactStage (k := k) n)) = Set.range g.base
  rw [Scheme.Hom.support_ker, g.isClosedMap.isClosed_range.closure_eq]

/-- Every point of the original previous strict curve is reached by the constructed morphism. -/
theorem strictStepProjection_surjective (n m : ℕ) :
    Surjective (strictStepProjection (k := k) n m) := by
  constructor
  intro y
  have hy : (strictTransformι (k := k) n ((m + 1) + n)).base y ∈
      Set.range (strictTransformι (n + 1) (m + (n + 1)) ≫
        (projectiveProductInitial (k := k)).stepProjection n).base := by
    rw [← strictStep_composite_range n m]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, (strictTransformι n ((m + 1) + n)).isClosedEmbedding.injective ?_⟩
  exact (congrArg (fun f => f.base x) (strictStepProjection_inclusion n m)).trans hx

end KltDP.Examples.FrobeniusStrictTransformStepProjection
