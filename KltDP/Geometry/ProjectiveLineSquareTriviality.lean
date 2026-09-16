import KltDP.Geometry.ProjectiveLineTransitionExtension
import KltDP.Geometry.ProjectiveLineChartTriviality
import KltDP.Geometry.TransitionUnitIsoGauge
import KltDP.Geometry.TransitionUnitTensor
import KltDP.Geometry.TransitionUnitRecovery

/-!
# An actual projective-line invertible sheaf with trivial square is trivial

An actual isomorphism of the glued sheaves gives chart gauge units and
therefore preserves the overlap exponent. Tensor product adds exponents.
Thus a trivial square forces twice the exponent to vanish in the integers.
The exponent is zero, its transition extends, and the constructed gauge
map trivializes the original sheaf. Every chart and tensor comparison
comes from the original scheme and its actual module sheaves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.ProjectiveLineSquareTriviality

open ProjectiveLineComparison ProjectiveLineSections ProjectiveLineTransitionExponent
open ProjectiveLineTransitionExtension ProjectiveLineChartTriviality TransitionUnitGluing

variable (k : Type u) [Field k]

local instance p1ModulesMonoidal : MonoidalCategory (projectiveSpace k 1).Modules :=
  Scheme.Modules.monoidalCategory (projectiveSpace k 1)

variable (g h : ∀ i j : ULift.{u} (Fin 2),
  Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ)

/-- A gauge on the original standard charts preserves their actual overlap exponent. -/
theorem cocycleExponent_eq_of_gauge
    (b : ∀ i : ULift.{u} (Fin 2), Γ(projectiveSpace k 1, standardOpens k i)ˣ)
    (hb : IsGauge (projectiveSpace k 1) (standardOpens k) g h b) :
    cocycleExponent k g = cocycleExponent k h := by
  have hr := congrArg (res (projectiveSpace k 1) (overlapOpen_eq_inf k).le)
    (hb ⟨0⟩ ⟨1⟩)
  simp only [map_mul, res_res] at hr
  have hu : Units.map (restrictLeft k).toMonoidHom (b ⟨0⟩) *
        overlapRestriction k (g ⟨0⟩ ⟨1⟩) =
      overlapRestriction k (h ⟨0⟩ ⟨1⟩) *
        Units.map (restrictRight k).toMonoidHom (b ⟨1⟩) := Units.ext hr
  have he := congrArg (overlapExponent k) hu
  simpa only [overlapExponent_mul, overlapExponent_restrictLeft,
    overlapExponent_restrictRight, zero_add, add_zero] using he

/-- An original sheaf isomorphism supplies the gauge needed for exponent invariance. -/
theorem cocycleExponent_eq_of_iso
    (hg : IsCocycle (projectiveSpace k 1) (standardOpens k) g)
    (hh : IsCocycle (projectiveSpace k 1) (standardOpens k) h)
    (e : moduleSheaf (projectiveSpace k 1) (standardOpens k) g ≅
      moduleSheaf (projectiveSpace k 1) (standardOpens k) h) :
    cocycleExponent k g = cocycleExponent k h := by
  obtain ⟨b, hb⟩ := exists_gauge_of_iso (projectiveSpace k 1) (standardOpens k) g h hg hh e
  exact cocycleExponent_eq_of_gauge k g h b hb

/-- The identity transition has exponent zero. -/
theorem cocycleExponent_one :
    cocycleExponent k (oneUnits (projectiveSpace k 1) (standardOpens k)) = 0 := by
  change overlapExponent k (overlapRestriction k 1) = 0
  rw [map_one, overlapExponent_one]

/-- The product transition cocycle has the sum of the two exponents. -/
theorem cocycleExponent_product :
    cocycleExponent k (productUnits (projectiveSpace k 1) (standardOpens k) g h) =
      cocycleExponent k g + cocycleExponent k h := by
  change overlapExponent k (overlapRestriction k (g ⟨0⟩ ⟨1⟩ * h ⟨0⟩ ⟨1⟩)) = _
  rw [map_mul, overlapExponent_mul]
  rfl

/-- A trivial actual tensor square forces the original transition exponent to vanish. -/
theorem cocycleExponent_zero_of_square_iso
    (hg : IsCocycle (projectiveSpace k 1) (standardOpens k) g)
    (hU : (⨆ i, standardOpens k i) = ⊤)
    (e : moduleSheaf (projectiveSpace k 1) (standardOpens k) g ⊗
        moduleSheaf (projectiveSpace k 1) (standardOpens k) g ≅
      _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :
    cocycleExponent k g = 0 := by
  let e' := (TransitionUnitGluing.tensorIso (projectiveSpace k 1) (standardOpens k)
      g g hg hg hU).symm ≪≫ e ≪≫ unitIsoOne (projectiveSpace k 1) (standardOpens k) hU
  have he := cocycleExponent_eq_of_iso k
    (productUnits (projectiveSpace k 1) (standardOpens k) g g)
    (oneUnits (projectiveSpace k 1) (standardOpens k))
    (productUnits_isCocycle (projectiveSpace k 1) (standardOpens k) g g hg hg)
    (oneUnits_isCocycle (projectiveSpace k 1) (standardOpens k)) e'
  rw [cocycleExponent_product, cocycleExponent_one] at he
  omega

/-- The original glued sheaf, with its original transition maps, is trivial if its square is. -/
def gluedUnitIsoOfSquareIso
    (hg : IsCocycle (projectiveSpace k 1) (standardOpens k) g)
    (hU : (⨆ i, standardOpens k i) = ⊤)
    (e : moduleSheaf (projectiveSpace k 1) (standardOpens k) g ⊗
        moduleSheaf (projectiveSpace k 1) (standardOpens k) g ≅
      _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :
    moduleSheaf (projectiveSpace k 1) (standardOpens k) g ≅
      _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf :=
  unitIsoOfCocycleExponentZero k g hg hU (cocycleExponent_zero_of_square_iso k g hg hU e)

/-- Any original invertible sheaf on the actual projective line is trivial when its actual square is. -/
def invertibleUnitIsoOfSquareIso (L : InvertibleSheaf (projectiveSpace k 1))
    (e : L.obj ⊗ L.obj ≅ _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :
    L.obj ≅ _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf := by
  let t := standardChartLocalTrivializations k L
  let g : ∀ i j : ULift.{u} (Fin 2),
      Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ :=
    TransitionUnitExtraction.transitionUnits (projectiveSpace k 1) L.obj t
  have hg : IsCocycle (projectiveSpace k 1) (standardOpens k) g :=
    TransitionUnitExtraction.transitionUnits_isCocycle (projectiveSpace k 1) L.obj t
  have hU : (⨆ i, standardOpens k i) = ⊤ :=
    TransitionUnitExtraction.chartOpens_cover (projectiveSpace k 1) L.obj t
  let r : L.obj ≅ moduleSheaf (projectiveSpace k 1) (standardOpens k) g :=
    TransitionUnitExtraction.recoveryIso (projectiveSpace k 1) L.obj t
  exact r ≪≫ gluedUnitIsoOfSquareIso k g hg hU
    (CategoryTheory.MonoidalCategory.tensorIso r.symm r.symm ≪≫ e)

end KltDP.Geometry.ProjectiveLineSquareTriviality
