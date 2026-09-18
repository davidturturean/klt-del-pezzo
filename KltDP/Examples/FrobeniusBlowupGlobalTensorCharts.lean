import KltDP.Examples.FrobeniusBlowupGlobalCanonicalTarget
import KltDP.Examples.FrobeniusBlowupGlobalExteriorCharts
import KltDP.Geometry.AffineBlowupExceptionalIdealTildeComparison
import KltDP.Geometry.SchemeModulePullbackTensorInclusion

/-!
# The original exceptional canonical tensor on the actual Rees charts

The native ideal tilde comparison preserves the actual ideal inclusion.
The original open differential isomorphism identifies the other tensor
factor. The original pullback tensor comparison therefore preserves the
whole inclusion of the actual global exceptional canonical tensor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusBlowupGlobalTensorCharts

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth
open FrobeniusBlowupGlobalDifferentialCharts FrobeniusBlowupGlobalExteriorCharts
open FrobeniusBlowupGlobalCanonicalTarget

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k]

/-- The original affine-chart ideal tensor inclusion into the actual intrinsic top sheaf. -/
def chartIdealTopInclusion (a : centerIdeal (k := k)) :
    (chartIdealModule centerIdeal a).tilde ⊗ chartTop a ⟶ chartTop a :=
  schemeStructureTensorInclusion (chartIdealTildeInclusion centerIdeal a) (chartTop a)

/-- Both factors are the original geometric comparisons, followed by the original tensorator. -/
def chartExceptionalTensorIso (a : centerIdeal (k := k)) :
    (schemeModulePullback (chartι centerIdeal a)).obj
        (exceptionalCanonicalTensor (k := k)) ≅
      (chartIdealModule centerIdeal a).tilde ⊗ chartTop a :=
  schemeModulePullbackTensorIso (chartι centerIdeal a)
      (exceptionalIdealModule centerIdeal) (blowupTop (k := k)) ≪≫
    tensorIso (originalChartIdealTildeGlobalIso centerIdeal a).symm (chartGlobalIso a)

private def chartExceptionalTensorIso_inclusion_proof (k : Type u) [Field k]
    (a : centerIdeal (k := k)) :=
  schemeModulePullbackTensorIso_comparison_inclusion (chartι centerIdeal a)
    (schemeKernelIdealι (exceptionalι centerIdeal)) (blowupTop (k := k))
    (originalChartIdealTildeGlobalIso centerIdeal a) (chartGlobalIso a)
    (chartIdealTildeInclusion centerIdeal a)
    (originalChartIdealTildeGlobalIso_inclusion centerIdeal a)

/-- The whole original global inclusion restricts to the whole original chart inclusion. -/
theorem chartExceptionalTensorIso_inclusion (a : centerIdeal (k := k)) :
    (chartExceptionalTensorIso a).hom ≫ chartIdealTopInclusion a =
      (schemeModulePullback (chartι centerIdeal a)).map
          (exceptionalCanonicalInclusion (k := k)) ≫ (chartGlobalIso a).hom := by
  simpa only [chartExceptionalTensorIso, chartIdealTopInclusion,
    exceptionalCanonicalInclusion, exceptionalInclusionToUnit,
    schemeStructureTensorInclusion] using chartExceptionalTensorIso_inclusion_proof k a

end KltDP.Examples.FrobeniusBlowupGlobalTensorCharts
