import KltDP.Examples.FrobeniusGlobalBlowupDifferentialAffine
import KltDP.Examples.FrobeniusGlobalBlowupSmooth
import KltDP.Geometry.PointBlowupExceptionalIdeal
import KltDP.Geometry.SchemeModulePullbackTensorInclusion
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.InvertibleTensorExact

/-!
# The original exceptional ideal tensor on the whole next blowup stage

The ideal is literally the kernel of the original entire center-fiber
inclusion. Its invertibility is already proved on the original two-piece
cover. The original next-stage top sheaf is invertible by the proved
preservation of smooth relative dimension two. Tensoring the original
kernel inclusion with that top sheaf therefore gives the actual monic
target map for the canonical factorization on the whole next scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupCanonicalTarget

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupDifferentialAffine

local instance wholeTargetModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem tensorInclusion_mono {X : Scheme.{u}} {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) [Mono i]
    (L : InvertibleSheaf X) : Mono (schemeStructureTensorInclusion i L.obj) := by
  letI := L.tensorRight_preservesFiniteLimits
  haveI : Mono (i ≫ (SchemeModuleStructureUnit.iso X).hom) := inferInstance
  change Mono ((tensorRight L.obj).map (i ≫ (SchemeModuleStructureUnit.iso X).hom) ≫
    (λ_ L.obj).hom)
  infer_instance

variable {k : Type u} [Field k]

local instance wholeTargetOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

variable (A : PlaneChartedScheme k)

/-- The ideal is the original entire center-fiber kernel, with no replacement divisor. -/
abbrev wholeExceptionalIdeal : A.nextScheme.Modules :=
  schemeKernelIdeal
    (PointBlowupGluing.globalCenterFiberι A.chart (originPoint (k := k)) A.center_closed)

/-- Its invertibility is the existing theorem for the same original kernel. -/
def wholeExceptionalIdealLine : InvertibleSheaf A.nextScheme :=
  PointBlowupGluing.globalCenterFiberIdealLine A.chart (originPoint (k := k)) A.center_closed

/-- The original whole exceptional ideal inclusion into the actual structure module. -/
def wholeExceptionalInclusion :
    wholeExceptionalIdeal A ⟶ _root_.SheafOfModules.unit A.nextScheme.ringCatSheaf :=
  schemeKernelIdealι
    (PointBlowupGluing.globalCenterFiberι A.chart (originPoint (k := k)) A.center_closed)

/-- The actual original target of the next-stage canonical factor. -/
abbrev wholeCanonicalTarget : A.nextScheme.Modules :=
  wholeExceptionalIdeal A ⊗ nextTop A

/-- The map uses the original kernel inclusion and original structure tensor action. -/
def wholeCanonicalInclusion : wholeCanonicalTarget A ⟶ nextTop A :=
  schemeStructureTensorInclusion (wholeExceptionalInclusion A) (nextTop A)

variable [IsSmoothOfRelativeDimension 2 A.structureMap]

/-- Smoothness of the actual next-stage structure proves invertibility of its own top sheaf. -/
def nextTopLine : InvertibleSheaf A.nextScheme :=
  ⟨nextTop A,
    SmoothCanonicalExteriorComparison.relativeDifferentialExterior_isInvertible A.nextStructure⟩

/-- Monicity is derived from the actual kernel inclusion and actual smooth top sheaf. -/
theorem wholeCanonicalInclusion_mono : Mono (wholeCanonicalInclusion A) := by
  letI : Mono (wholeExceptionalInclusion A) := by
    unfold wholeExceptionalInclusion schemeKernelIdealι
    infer_instance
  exact tensorInclusion_mono (wholeExceptionalInclusion A) (nextTopLine A)

end KltDP.Examples.FrobeniusGlobalBlowupCanonicalTarget
