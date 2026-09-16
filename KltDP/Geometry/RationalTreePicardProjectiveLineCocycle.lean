/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors

The two-chart unit construction and eight-case cocycle proof are adapted
from frenzymath/Algebraic-Geometry 9223d85c786394721963a9d642b08d066b72a594,
MainProjects/AlgebraicJacobian/PicardAlbanese/AlgebraicJacobian/Tangent/
TwoChartCechPic.lean:116-137. This version uses the project's original
section-ring restriction and ULift (Fin 2) standard-chart indices.
-/
import KltDP.Geometry.TransitionUnitLocalTriviality
import Mathlib.Tactic.FinCases

/-!
# A line-bundle cocycle from one actual two-chart transition

An arbitrary unit on the intersection of two original scheme opens supplies
the two off-diagonal transitions. The reverse transition is its inverse
transported through the equality of the two intersections. All eight cocycle
equations are proved in the original section rings.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RationalTreePicard

open TransitionUnitGluing

variable (X : Scheme.{u}) (U : ULift.{u} (Fin 2) → X.Opens)
  (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ)

/-- The original overlap unit and its inverse, with identity transitions
on each individual chart. -/
def twoOpenUnits (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ)
    (i j : ULift.{u} (Fin 2)) : Γ(X, U i ⊓ U j)ˣ := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact 1
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact a
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    refine Fin.cases ?_ (fun j => ?_) j
    · exact Units.map (res X (show U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩ from
        le_inf inf_le_right inf_le_left)).toMonoidHom a⁻¹
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact 1

private theorem twoOpenUnits_zero_zero : twoOpenUnits X U a ⟨0⟩ ⟨0⟩ = 1 := rfl

private theorem twoOpenUnits_zero_one : twoOpenUnits X U a ⟨0⟩ ⟨1⟩ = a := rfl

private theorem twoOpenUnits_one_zero : twoOpenUnits X U a ⟨1⟩ ⟨0⟩ =
    Units.map (res X (show U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩ from
      le_inf inf_le_right inf_le_left)).toMonoidHom a⁻¹ := rfl

private theorem twoOpenUnits_one_one : twoOpenUnits X U a ⟨1⟩ ⟨1⟩ = 1 := rfl

/-- The arbitrary original transition defines a genuine cocycle. -/
theorem twoOpenUnits_isCocycle : IsCocycle X U (twoOpenUnits X U a) where
  unit_self := by
    rintro ⟨i⟩
    fin_cases i <;> rfl
  mul_res := by
    rintro ⟨i⟩ ⟨j⟩ ⟨l⟩
    fin_cases i <;> fin_cases j <;> fin_cases l
    · change res X _ (1 : Γ(X, U ⟨0⟩ ⊓ U ⟨0⟩)) *
        res X _ (1 : Γ(X, U ⟨0⟩ ⊓ U ⟨0⟩)) =
          res X _ (1 : Γ(X, U ⟨0⟩ ⊓ U ⟨0⟩))
      simp only [map_one, mul_one]
    · change res X _ (1 : Γ(X, U ⟨0⟩ ⊓ U ⟨0⟩)) *
        res X _ (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) =
          res X _ (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩))
      simp only [map_one, one_mul]
    · change res X _ (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) *
        res X _ (res X (show U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩ from
          le_inf inf_le_right inf_le_left) ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩))) =
          res X _ (1 : Γ(X, U ⟨0⟩ ⊓ U ⟨0⟩))
      simp only [map_one, res_res]
      rw [← map_mul, Units.mul_inv, map_one]
    · change res X _ (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) *
        res X _ (1 : Γ(X, U ⟨1⟩ ⊓ U ⟨1⟩)) =
          res X _ (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩))
      simp only [map_one, mul_one]
    · change res X _ (res X (show U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩ from
        le_inf inf_le_right inf_le_left) ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩))) *
        res X _ (1 : Γ(X, U ⟨0⟩ ⊓ U ⟨0⟩)) =
          res X _ (res X (show U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩ from
            le_inf inf_le_right inf_le_left) ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)))
      simp only [map_one, mul_one, res_res]
    · change res X _ (res X (show U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩ from
        le_inf inf_le_right inf_le_left) ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩))) *
        res X _ (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) =
          res X _ (1 : Γ(X, U ⟨1⟩ ⊓ U ⟨1⟩))
      simp only [map_one, res_res]
      rw [← map_mul, Units.inv_mul, map_one]
    · change res X _ (1 : Γ(X, U ⟨1⟩ ⊓ U ⟨1⟩)) *
        res X _ (res X (show U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩ from
          le_inf inf_le_right inf_le_left) ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩))) =
          res X _ (res X (show U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩ from
            le_inf inf_le_right inf_le_left) ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)))
      simp only [map_one, one_mul, res_res]
    · change res X _ (1 : Γ(X, U ⟨1⟩ ⊓ U ⟨1⟩)) *
        res X _ (1 : Γ(X, U ⟨1⟩ ⊓ U ⟨1⟩)) =
          res X _ (1 : Γ(X, U ⟨1⟩ ⊓ U ⟨1⟩))
      simp only [map_one, mul_one]

end KltDP.Geometry.RationalTreePicard
