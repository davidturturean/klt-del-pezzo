import KltDP.Geometry.ProjectiveSegreRange
import KltDP.Examples.FrobeniusStageSurface
import KltDP.Examples.FrobeniusSelectedStageSurface

/-!
# Stage `0` of the contact towers is projective: `hproj` discharged at stage `0`

Stage `0` of the Frobenius contact tower (`projectiveProductInitial`) and of every translated
tower (`translatedInitial p a`) is the product `P¹ ×_k P¹` with structure morphism
`projectiveProductToSpec`, which is projective over `k` by the Segre embedding
(`projectiveProduct_isProjectiveOverField`). Hence the stage-`0` surfaces `stageSurface 0` and
`selectedStageSurface p a 0` need no projectivity hypothesis (`projectiveProductSurface`,
`translatedProductSurface`).

The hypothesis `hproj` remains for every blowup stage `n ≥ 1` (`stageSurface (n+1)`,
`selectedStageSurface p a (n+1)`, `stageSurfaceOf A … (n+1)`) and for lane F's multi-centre
surfaces `multiSurfaceSurface p m a ha hproj` (`S_{p,n}`): no projective embedding of a point
blowup is constructed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStageZeroProjective

open KltDP.Geometry KltDP.Geometry.ProjectiveSegreCover
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts
open FrobeniusStageSurface FrobeniusSelectedStageSurface

variable {k : Type u} [Field k]

/-- Stage `0` of the contact tower is `P¹ ×_k P¹`, projective over `k` by the Segre embedding. -/
theorem stage_zero_projective :
    IsProjectiveOverField ((projectiveProductInitial (k := k)).stage 0).structureMap :=
  projectiveProduct_isProjectiveOverField k

/-- Stage `0` of every translated tower is projective over `k`. -/
theorem translated_stage_zero_projective (p : ℕ) (a : k) :
    IsProjectiveOverField ((translatedInitial (k := k) p a).stage 0).structureMap :=
  projectiveProduct_isProjectiveOverField k

/-- **`P¹ ×_k P¹` as a normal projective surface**, with no projectivity hypothesis. -/
def projectiveProductSurface [IsAlgClosed k] : NormalProjectiveSurface k :=
  stageSurface 0 stage_zero_projective

@[simp] theorem projectiveProductSurface_toScheme [IsAlgClosed k] :
    (projectiveProductSurface (k := k)).toScheme = projectiveProduct k := rfl

@[simp] theorem projectiveProductSurface_structureMorphism [IsAlgClosed k] :
    (projectiveProductSurface (k := k)).structureMorphism = projectiveProductToSpec := rfl

/-- Stage `0` of lane F's translated tower at `(a, a^p)` as a normal projective surface, with no
projectivity hypothesis. -/
def translatedProductSurface [IsAlgClosed k] (p : ℕ) (a : k) : NormalProjectiveSurface k :=
  selectedStageSurface p a 0 (translated_stage_zero_projective p a)

@[simp] theorem translatedProductSurface_toScheme [IsAlgClosed k] (p : ℕ) (a : k) :
    (translatedProductSurface (k := k) p a).toScheme = projectiveProduct k := rfl

end KltDP.Examples.FrobeniusStageZeroProjective
