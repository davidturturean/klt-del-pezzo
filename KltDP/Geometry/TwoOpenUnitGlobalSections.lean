import KltDP.Geometry.RationalTreePicardProjectiveLineCocycle
import KltDP.Geometry.TransitionUnitGlobalSections

/-! # Original global sections on the existing two-open line sheaf -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.TwoOpenUnitGlobalSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing RationalTreePicard

variable (X : Scheme.{u}) (U : ULift.{u} (Fin 2) → X.Opens)

/-- Two original chart functions, with the original lifted chart index. -/
def coordinates (r₀ : Γ(X, U ⟨0⟩)) (r₁ : Γ(X, U ⟨1⟩))
    (i : ULift.{u} (Fin 2)) : Γ(X, U i) := by
  rcases i with ⟨i⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · exact r₀
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact r₁

@[simp] theorem coordinates_zero (r₀ : Γ(X, U ⟨0⟩)) (r₁ : Γ(X, U ⟨1⟩)) :
    coordinates X U r₀ r₁ ⟨0⟩ = r₀ := rfl

@[simp] theorem coordinates_one (r₀ : Γ(X, U ⟨0⟩)) (r₁ : Γ(X, U ⟨1⟩)) :
    coordinates X U r₀ r₁ ⟨1⟩ = r₁ := rfl

variable (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ)
  (r₀ : Γ(X, U ⟨0⟩)) (r₁ : Γ(X, U ⟨1⟩))
  (h : res X (inf_le_left : U ⟨0⟩ ⊓ U ⟨1⟩ ≤ U ⟨0⟩) r₀ =
    (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) *
      res X (inf_le_right : U ⟨0⟩ ⊓ U ⟨1⟩ ≤ U ⟨1⟩) r₁)

include h in
/-- The one original overlap equality supplies all four compatibility equations. -/
theorem coordinates_compatible (i j : ULift.{u} (Fin 2)) :
    res X (inf_le_left : U i ⊓ U j ≤ U i) (coordinates X U r₀ r₁ i) =
      (twoOpenUnits X U a i j : Γ(X, U i ⊓ U j)) *
        res X (inf_le_right : U i ⊓ U j ≤ U j) (coordinates X U r₀ r₁ j) := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j
  · change res X _ r₀ = 1 * res X _ r₀
    exact (one_mul _).symm
  · exact h
  · let e : U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩ ⊓ U ⟨1⟩ :=
      le_inf inf_le_right inf_le_left
    have he := congrArg (res X e) h
    rw [map_mul, res_res, res_res] at he
    have hi := congrArg (fun z : Γ(X, U ⟨1⟩ ⊓ U ⟨0⟩) =>
      res X e ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) * z) he
    change res X e ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) *
        res X (inf_le_right : U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩) r₀ =
      res X e ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) *
        (res X e (a : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) *
          res X (inf_le_left : U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨1⟩) r₁) at hi
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at hi
    change res X (inf_le_left : U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨1⟩) r₁ =
      res X e ((a⁻¹ : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)ˣ) : Γ(X, U ⟨0⟩ ⊓ U ⟨1⟩)) *
        res X (inf_le_right : U ⟨1⟩ ⊓ U ⟨0⟩ ≤ U ⟨0⟩) r₀
    exact hi.symm
  · change res X _ r₁ = 1 * res X _ r₁
    exact (one_mul _).symm

/-- The resulting actual compatible global section of the existing glued sheaf. -/
def globalSection : (moduleSheaf X U (twoOpenUnits X U a)).sections :=
  globalSectionOfCoordinates X U (twoOpenUnits X U a)
    (coordinates X U r₀ r₁) (coordinates_compatible X U a r₀ r₁ h)

end KltDP.Geometry.TwoOpenUnitGlobalSections
