import KltDP.Examples.FrobeniusMultiCentreCanonicalIdealMonic
import KltDP.Examples.FrobeniusMultiCentreCanonicalDifferentialCharts
import KltDP.Geometry.SmoothCanonicalExteriorComparison

/-!
# The actual finite-centre canonical factor target

Tensor the actual whole exceptional ideal family with the original intrinsic
top differential sheaf. The original smoothness producer makes that top sheaf
invertible; the proved monicity of the original exceptional product then makes
the actual target inclusion monic. No canonical formula is used here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalTarget

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreCanonicalIdealFamily
open FrobeniusMultiCentreCanonicalIdealMonic FrobeniusMultiCentreCanonicalDifferentialCharts
open FrobeniusContactTowerCanonicalFactorMono

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance multiCanonicalTargetModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k]

/-- The actual tensor target, independently of any proposed canonical isomorphism. -/
abbrev multiCanonicalTarget (p n : ℕ) (a : Fin n → k) : (multiSurface p n a).Modules :=
  (multiIdealLine p n a).obj ⊗ multiTop p n a

/-- Its original ideal-tensor inclusion into the actual intrinsic top sheaf. -/
def multiCanonicalInclusion (p n : ℕ) (a : Fin n → k) :
    multiCanonicalTarget p n a ⟶ multiTop p n a :=
  schemeStructureTensorInclusion (multiIdealInclusion p n a) (multiTop p n a)

variable [IsAlgClosed k]

/-- The original global smoothness theorem makes the original top sheaf an invertible line. -/
def multiTopLine (p n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    InvertibleSheaf (multiSurface p n a) := by
  letI := multiStructure_smoothTwo p n a ha
  exact ⟨multiTop p n a,
    SmoothCanonicalExteriorComparison.relativeDifferentialExterior_isInvertible
      (multiStructure p n a)⟩

/-- The actual global target inclusion is monic, as required by the original monic-factor gluing. -/
theorem multiCanonicalInclusion_mono (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) : Mono (multiCanonicalInclusion (q + 1) n a) := by
  letI := multiIdealInclusion_mono q n a ha
  exact tensorInclusion_mono (multiIdealInclusion (q + 1) n a)
    (multiTopLine (q + 1) n a ha)

end KltDP.Examples.FrobeniusMultiCentreCanonicalTarget
