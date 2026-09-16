import KltDP.Geometry.ProjectiveLineSquareTriviality

/-!
# The transition exponent of an actual projective-line invertible sheaf

The affine-line theorem supplies frames on the original two standard
opens. Their transition gives an integer. Actual sheaf isomorphisms
preserve this integer, tensor products add it, and exponent zero gives
an actual unit-sheaf isomorphism. The integer is not identified here
with any independently defined divisor degree.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.ProjectiveLineSheafExponent

open ProjectiveLineChartTriviality ProjectiveLineTransitionExtension
open ProjectiveLineSquareTriviality TransitionUnitGluing

variable (k : Type u) [Field k]

local instance sheafExponentMonoidal : MonoidalCategory (projectiveSpace k 1).Modules :=
  Scheme.Modules.monoidalCategory (projectiveSpace k 1)

/-- The original transition units in the derived standard-chart frames. -/
def standardUnits (L : InvertibleSheaf (projectiveSpace k 1)) :
    ∀ i j : ULift.{u} (Fin 2),
      Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ :=
  TransitionUnitExtraction.transitionUnits (projectiveSpace k 1) L.obj
    (standardChartLocalTrivializations k L)

/-- These original units satisfy the proved transition cocycle equations. -/
theorem standardUnits_isCocycle (L : InvertibleSheaf (projectiveSpace k 1)) :
    IsCocycle (projectiveSpace k 1) (standardOpens k) (standardUnits k L) :=
  TransitionUnitExtraction.transitionUnits_isCocycle (projectiveSpace k 1) L.obj
    (standardChartLocalTrivializations k L)

/-- The atlas uses the original covering by the two standard opens. -/
theorem standardCover (L : InvertibleSheaf (projectiveSpace k 1)) :
    (⨆ i : ULift.{u} (Fin 2), standardOpens k i) = ⊤ :=
  TransitionUnitExtraction.chartOpens_cover (projectiveSpace k 1) L.obj
    (standardChartLocalTrivializations k L)

/-- The original sheaf is recovered from its actual standard-chart transitions. -/
def standardRecoveryIso (L : InvertibleSheaf (projectiveSpace k 1)) :
    L.obj ≅ moduleSheaf (projectiveSpace k 1) (standardOpens k) (standardUnits k L) :=
  TransitionUnitExtraction.recoveryIso (projectiveSpace k 1) L.obj
    (standardChartLocalTrivializations k L)

/-- The integer exponent of the original overlap transition. -/
def exponent (L : InvertibleSheaf (projectiveSpace k 1)) : ℤ :=
  cocycleExponent k (standardUnits k L)

/-- Any actual presentation on the standard opens computes the same exponent. -/
theorem exponent_eq_of_iso_to_glued (L : InvertibleSheaf (projectiveSpace k 1))
    (g : ∀ i j : ULift.{u} (Fin 2),
      Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ)
    (hg : IsCocycle (projectiveSpace k 1) (standardOpens k) g)
    (e : L.obj ≅ moduleSheaf (projectiveSpace k 1) (standardOpens k) g) :
    exponent k L = cocycleExponent k g :=
  cocycleExponent_eq_of_iso k (standardUnits k L) g (standardUnits_isCocycle k L) hg
    ((standardRecoveryIso k L).symm ≪≫ e)

/-- Actual isomorphic invertible sheaves have the same transition exponent. -/
theorem exponent_eq_of_iso (L M : InvertibleSheaf (projectiveSpace k 1))
    (e : L.obj ≅ M.obj) : exponent k L = exponent k M :=
  exponent_eq_of_iso_to_glued k L (standardUnits k M) (standardUnits_isCocycle k M)
    (e ≪≫ standardRecoveryIso k M)

/-- An actual trivialization makes the transition exponent zero. -/
theorem exponent_eq_zero_of_iso_unit (L : InvertibleSheaf (projectiveSpace k 1))
    (e : L.obj ≅ _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :
    exponent k L = 0 :=
  (exponent_eq_of_iso_to_glued k L
    (oneUnits (projectiveSpace k 1) (standardOpens k))
    (oneUnits_isCocycle (projectiveSpace k 1) (standardOpens k))
    (e ≪≫ unitIsoOne (projectiveSpace k 1) (standardOpens k) (standardCover k L))).trans
      (cocycleExponent_one k)

/-- Zero exponent constructs a unit isomorphism of the original sheaf. -/
def unitIsoOfExponentZero (L : InvertibleSheaf (projectiveSpace k 1))
    (h : exponent k L = 0) :
    L.obj ≅ _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf :=
  standardRecoveryIso k L ≪≫
    unitIsoOfCocycleExponentZero k (standardUnits k L) (standardUnits_isCocycle k L)
      (standardCover k L) h

/-- Exponent zero is equivalent to an actual global unit-sheaf isomorphism. -/
theorem exponent_eq_zero_iff (L : InvertibleSheaf (projectiveSpace k 1)) :
    exponent k L = 0 ↔
      Nonempty (L.obj ≅ _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :=
  ⟨fun h => ⟨unitIsoOfExponentZero k L h⟩,
    fun ⟨e⟩ => exponent_eq_zero_of_iso_unit k L e⟩

/-- An actual tensor-product presentation adds the two original exponents. -/
theorem exponent_eq_add_of_tensorIso (L M N : InvertibleSheaf (projectiveSpace k 1))
    (e : N.obj ≅ L.obj ⊗ M.obj) :
    exponent k N = exponent k L + exponent k M := by
  let g := standardUnits k L
  let h := standardUnits k M
  let e' := e ≪≫ CategoryTheory.MonoidalCategory.tensorIso
      (standardRecoveryIso k L) (standardRecoveryIso k M) ≪≫
    TransitionUnitGluing.tensorIso (projectiveSpace k 1) (standardOpens k) g h
      (standardUnits_isCocycle k L) (standardUnits_isCocycle k M) (standardCover k L)
  exact (exponent_eq_of_iso_to_glued k N
    (productUnits (projectiveSpace k 1) (standardOpens k) g h)
    (productUnits_isCocycle (projectiveSpace k 1) (standardOpens k) g h
      (standardUnits_isCocycle k L) (standardUnits_isCocycle k M)) e').trans
        (cocycleExponent_product k g h)

end KltDP.Geometry.ProjectiveLineSheafExponent
