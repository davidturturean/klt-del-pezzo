import KltDP.Geometry.InvertibleQuadraticAtlas
import KltDP.Geometry.FiniteOverProjective
import KltDP.Geometry.FinitePullbackImageLineAmple
import KltDP.Geometry.ProjectiveProper

/-!
# Projectivity and an ample pullback on the original quadratic cover

The unchanged square-root atlas supplies the finite map to the original
base. The existing finite-over-projective construction then supplies an
actual projective embedding of this same cover over the same field.
The original base embedding also supplies a particular ample line whose
actual pullback to this cover is ample. No projectivity or ampleness of
the cover, alternate cover, or local coordinates are assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.InvertibleQuadraticAtlas

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.IsSeparated]

local instance originalQuadraticProjectiveMonoidal : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

variable (L : InvertibleSheaf X) (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (b : N.val.obj (op (⊤ : X.Opens)))
    (σ : X ⟶ Spec (CommRingCat.of k)) (hσ : IsProjectiveOverField σ)

include hσ

/-- The same original quadratic cover is projective over the original field. -/
theorem fromSquareRoot_isProjective :
    IsProjectiveOverField ((fromSquareRoot X L N e b).morphism ≫ σ) := by
  letI : IsFinite (fromSquareRoot X L N e b).morphism :=
    (fromSquareRoot_finite_flat X L N e b).1
  exact IsProjectiveOverField.comp_isFinite (fromSquareRoot X L N e b).morphism σ hσ

/-- The actual original field map of the quadratic cover is proper. -/
theorem fromSquareRoot_isProper :
    IsProper ((fromSquareRoot X L N e b).morphism ≫ σ) :=
  (fromSquareRoot_isProjective X L N e b σ hσ).isProper

/-- The original base embedding supplies a line ample on both the base and its actual cover. -/
theorem fromSquareRoot_exists_ample_base_pullback :
    ∃ M : InvertibleSheaf X, AmpleSerre.IsAmple M ∧
      AmpleSerre.IsAmple (pullbackInvertibleSheaf (fromSquareRoot X L N e b).morphism M) := by
  obtain ⟨n, i, hi, _hfield⟩ := hσ
  letI : IsClosedImmersion i := hi
  letI : IsFinite (fromSquareRoot X L N e b).morphism :=
    (fromSquareRoot_finite_flat X L N e b).1
  refine ⟨pullbackInvertibleSheaf i (ProjectiveSpaceDegreeOneSheaf.degreeOne k n),
    projectiveSpaceDegreeOne_pullback_isAmple k n i, ?_⟩
  exact FinitePullbackImageLineAmple.finite_pullback_degreeOne_isAmple k n
    (fromSquareRoot X L N e b).morphism i

end KltDP.Geometry.InvertibleQuadraticAtlas

#print axioms KltDP.Geometry.InvertibleQuadraticAtlas.fromSquareRoot_isProjective
#print axioms KltDP.Geometry.InvertibleQuadraticAtlas.fromSquareRoot_exists_ample_base_pullback
