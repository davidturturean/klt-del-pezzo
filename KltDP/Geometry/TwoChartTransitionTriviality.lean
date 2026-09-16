import KltDP.Geometry.TransitionUnitGauge
import KltDP.Geometry.TransitionUnitConstant
import Mathlib.Tactic.FinCases

/-!
# Trivializing a two-chart cocycle whose transition extends

If the original transition from chart one to chart zero is the restriction
of an actual unit on chart zero, rescaling that chart by its inverse
trivializes the cocycle. The reverse-overlap equation follows from the
original cocycle law. The resulting isomorphism is the existing actual
gauge map followed by the proved identity-cocycle gluing isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

variable (X : Scheme.{u}) (U : ULift.{u} (Fin 2) → X.Opens)
  (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ) (hg : IsCocycle X U g)

/-- The actual inverse unit on chart zero, and the identity on chart one. -/
def twoChartExtensionGauge (a : Γ(X, U ⟨0⟩)ˣ) (i : ULift.{u} (Fin 2)) : Γ(X, U i)ˣ :=
  Fin.cases (motive := fun j : Fin 2 => Γ(X, U ⟨j⟩)ˣ) a⁻¹ (fun _ => 1) i.down

include hg in
/-- The original extension equation and cocycle law prove all four gauge equations. -/
theorem twoChartExtension_isGauge (a : Γ(X, U ⟨0⟩)ˣ)
    (ha : res X (inf_le_left : U ⟨0⟩ ⊓ U ⟨1⟩ ≤ U ⟨0⟩) a =
      (g ⟨0⟩ ⟨1⟩ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩))) :
    IsGauge X U g (oneUnits X U) (twoChartExtensionGauge X U a) := by
  intro i j
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  · change res X inf_le_left (a⁻¹ : Γ(X, U ⟨0⟩)ˣ) *
        (g ⟨0⟩ ⟨0⟩ : Γ(X, U ⟨0⟩ ⊓ U ⟨0⟩)) =
      1 * res X inf_le_right (a⁻¹ : Γ(X, U ⟨0⟩)ˣ)
    rw [hg.unit_self, mul_one, one_mul]
  · change res X inf_le_left (a⁻¹ : Γ(X, U ⟨0⟩)ˣ) *
        (g ⟨0⟩ ⟨1⟩ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) =
      1 * res X inf_le_right (1 : Γ(X, U ⟨1⟩))
    rw [← ha, ← map_mul, Units.inv_mul, map_one, map_one, one_mul]
  · change res X inf_le_left (1 : Γ(X, U ⟨1⟩)) *
        (g ⟨1⟩ ⟨0⟩ : Γ(X, U ⟨1⟩ ⊓ U ⟨0⟩)) =
      1 * res X inf_le_right (a⁻¹ : Γ(X, U ⟨0⟩)ˣ)
    rw [map_one, one_mul, one_mul]
    have hr := IsCocycle.mul_res_of_le X U g hg
      (i := ⟨1⟩) (j := ⟨0⟩) (l := ⟨1⟩)
      (W := U ⟨1⟩ ⊓ U ⟨0⟩) (le_inf le_rfl inf_le_left)
    rw [res_self, hg.unit_self, map_one] at hr
    have ha' := congrArg
      (res X (le_inf inf_le_right inf_le_left :
        U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩)) ha
    rw [res_res] at ha'
    rw [← ha'] at hr
    calc
      (g ⟨1⟩ ⟨0⟩ : Γ(X, U ⟨1⟩ ⊓ U ⟨0⟩)) =
          (g ⟨1⟩ ⟨0⟩ : Γ(X, U ⟨1⟩ ⊓ U ⟨0⟩)) *
            (res X inf_le_right a * res X inf_le_right (a⁻¹ : Γ(X, U ⟨0⟩)ˣ)) := by
        rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = res X inf_le_right (a⁻¹ : Γ(X, U ⟨0⟩)ˣ) := by
        rw [← mul_assoc, hr, one_mul]
  · change res X (inf_le_left : U ⟨1⟩ ⊓ U ⟨1⟩ ≤ U ⟨1⟩) (1 : Γ(X, U ⟨1⟩)) *
        (g ⟨1⟩ ⟨1⟩ : Γ(X, U ⟨1⟩ ⊓ U ⟨1⟩)) =
      1 * res X (inf_le_right : U ⟨1⟩ ⊓ U ⟨1⟩ ≤ U ⟨1⟩) (1 : Γ(X, U ⟨1⟩))
    rw [hg.unit_self, map_one]

/-- An extending original transition unit constructs an actual global unit-sheaf isomorphism. -/
def twoChartUnitIsoOfExtension (hU : (⨆ i, U i) = ⊤)
    (a : Γ(X, U ⟨0⟩)ˣ)
    (ha : res X (inf_le_left : U ⟨0⟩ ⊓ U ⟨1⟩ ≤ U ⟨0⟩) a =
      (g ⟨0⟩ ⟨1⟩ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩))) :
    moduleSheaf X U g ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  gaugeIso X U g (oneUnits X U) (twoChartExtensionGauge X U a)
      (twoChartExtension_isGauge X U g hg a ha) ≪≫ (unitIsoOne X U hU).symm

end KltDP.Geometry.TransitionUnitGluing
