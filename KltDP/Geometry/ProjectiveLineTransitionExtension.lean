import KltDP.Geometry.ProjectiveLineTransitionExponent
import KltDP.Geometry.TwoChartTransitionTriviality

/-!
# Extending zero-exponent transitions on the actual projective line

A zero-exponent overlap unit has constant Laurent coordinates. The
original left chart section equivalence lifts that constant to an actual
chart unit. Transport through the proved equality of the two overlap
opens preserves the original restriction maps. The generic two-chart
gauge construction then supplies the actual global trivialization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveLineTransitionExtension

open ProjectiveLineComparison ProjectiveLineSections ProjectiveLineTransitionExponent
open TransitionUnitGluing

variable (k : Type u) [Field k]

/-- A scalar unit expressed as an actual section unit on the first chart. -/
def leftScalarUnit (c : kˣ) : Γ(projectiveSpace k 1, chartOpen k 0)ˣ :=
  Units.map (leftSectionsEquiv k).symm.toRingHom.toMonoidHom
    (Units.map (Polynomial.C : k →+* Polynomial k).toMonoidHom c)

@[simp]
theorem leftScalarUnit_coordinates (c : kˣ) :
    leftSectionsEquiv k (leftScalarUnit k c : Γ(projectiveSpace k 1, chartOpen k 0)) =
      Polynomial.C (c : k) :=
  (leftSectionsEquiv k).apply_symm_apply _

/-- Exactly the zero-exponent overlap units extend to original units on the first chart. -/
theorem overlapExponent_zero_iff_extends (s : Γ(projectiveSpace k 1, overlapOpen k)ˣ) :
    overlapExponent k s = 0 ↔ ∃ a : Γ(projectiveSpace k 1, chartOpen k 0)ˣ,
      Units.map (restrictLeft k).toMonoidHom a = s := by
  constructor
  · intro hs
    obtain ⟨c, hc⟩ := (unitExponent_eq_zero_iff k (overlapLaurentUnit k s)).mp hs
    refine ⟨leftScalarUnit k c, ?_⟩
    apply Units.ext
    apply (overlapSectionsEquiv k).injective
    change overlapSectionsEquiv k
        (restrictLeft k (leftScalarUnit k c : Γ(projectiveSpace k 1, chartOpen k 0))) =
      overlapSectionsEquiv k (s : Γ(projectiveSpace k 1, overlapOpen k))
    rw [overlapSectionsEquiv_restrictLeft, leftScalarUnit_coordinates, Polynomial.toLaurent_C]
    exact hc.symm
  · rintro ⟨a, rfl⟩
    exact overlapExponent_restrictLeft k a

/-- The two original standard opens, with only the index universe lifted. -/
abbrev standardOpens (i : ULift.{u} (Fin 2)) : (projectiveSpace k 1).Opens :=
  chartOpen k i.down

/-- The original intersection unit restricted to the equal Proj basic overlap. -/
def overlapRestriction :
    Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)ˣ →*
      Γ(projectiveSpace k 1, overlapOpen k)ˣ :=
  Units.map (res (projectiveSpace k 1) (overlapOpen_eq_inf k).le).toMonoidHom

/-- Restriction between these equal original opens is injective on actual units. -/
theorem overlapRestriction_injective : Function.Injective (overlapRestriction k) := by
  intro a b h
  apply Units.ext
  have he := congrArg (fun q : Γ(projectiveSpace k 1, overlapOpen k)ˣ =>
    res (projectiveSpace k 1) (overlapOpen_eq_inf k).ge (q : Γ(projectiveSpace k 1, overlapOpen k))) h
  change res (projectiveSpace k 1) (overlapOpen_eq_inf k).ge
      (res (projectiveSpace k 1) (overlapOpen_eq_inf k).le
        (a : Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1))) =
    res (projectiveSpace k 1) (overlapOpen_eq_inf k).ge
      (res (projectiveSpace k 1) (overlapOpen_eq_inf k).le
        (b : Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1))) at he
  simpa only [res_res, res_self] using he

/-- The restricted chart-to-intersection map is the original chart-to-overlap map. -/
theorem overlapRestriction_chartLeft (a : Γ(projectiveSpace k 1, chartOpen k 0)ˣ) :
    overlapRestriction k
      (Units.map (res (projectiveSpace k 1)
        (inf_le_left : chartOpen k 0 ⊓ chartOpen k 1 ≤ chartOpen k 0)).toMonoidHom a) =
        Units.map (restrictLeft k).toMonoidHom a := by
  apply Units.ext
  change res (projectiveSpace k 1) (overlapOpen_eq_inf k).le
      (res (projectiveSpace k 1)
        (inf_le_left : chartOpen k 0 ⊓ chartOpen k 1 ≤ chartOpen k 0)
        (a : Γ(projectiveSpace k 1, chartOpen k 0))) =
    res (projectiveSpace k 1) (overlapOpen_le_left k)
      (a : Γ(projectiveSpace k 1, chartOpen k 0))
  exact res_res (projectiveSpace k 1) (overlapOpen_eq_inf k).le
    (inf_le_left : chartOpen k 0 ⊓ chartOpen k 1 ≤ chartOpen k 0)
    (a : Γ(projectiveSpace k 1, chartOpen k 0))

variable (g : ∀ i j : ULift.{u} (Fin 2),
  Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ)

/-- The exponent of the original off-diagonal transition of this actual two-chart family. -/
def cocycleExponent : ℤ := overlapExponent k (overlapRestriction k (g ⟨0⟩ ⟨1⟩))

/-- Zero exponent gives the original chart extension equation, without a supplied extension. -/
theorem exists_chartUnit_of_cocycleExponent_zero (h : cocycleExponent k g = 0) :
    ∃ a : Γ(projectiveSpace k 1, standardOpens k ⟨0⟩)ˣ,
      res (projectiveSpace k 1) (inf_le_left :
        standardOpens k ⟨0⟩ ⊓ standardOpens k ⟨1⟩ ≤ standardOpens k ⟨0⟩) a =
          (g ⟨0⟩ ⟨1⟩ : Γ(projectiveSpace k 1,
            standardOpens k ⟨0⟩ ⊓ standardOpens k ⟨1⟩)) := by
  obtain ⟨a, ha⟩ := (overlapExponent_zero_iff_extends k _).mp h
  refine ⟨a, ?_⟩
  have he := overlapRestriction_injective k
    ((overlapRestriction_chartLeft k a).trans ha)
  exact congrArg Units.val he

/-- The actual two-chart glued sheaf is trivial whenever its proved transition exponent is zero. -/
def unitIsoOfCocycleExponentZero
    (hg : IsCocycle (projectiveSpace k 1) (standardOpens k) g)
    (hU : (⨆ i, standardOpens k i) = ⊤) (h : cocycleExponent k g = 0) :
    moduleSheaf (projectiveSpace k 1) (standardOpens k) g ≅
      _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf := by
  let a := Classical.choose (exists_chartUnit_of_cocycleExponent_zero k g h)
  have ha := Classical.choose_spec (exists_chartUnit_of_cocycleExponent_zero k g h)
  exact twoChartUnitIsoOfExtension (projectiveSpace k 1) (standardOpens k) g hg hU a ha

end KltDP.Geometry.ProjectiveLineTransitionExtension
