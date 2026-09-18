import KltDP.Geometry.Resolution
import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Compatibility.BirationalRationality
import Mathlib.AlgebraicGeometry.Fiber

/-!
# The complete Hartshorne V.6.1 hypothesis on original objects

The full reviewed proposition remains an explicit hypothetical parameter.
Both equivalences, every positive canonical multiple, the universal original
minimality condition, and the complete geometric ruled disjunct are retained.
The application theorems introduce no literature declaration or replacement
surface, curve, rationality predicate, or Kodaira-dimension predicate.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Geometry.HartshorneClassificationConditional

variable (hClassification :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (hminimal :
      ∀ (T : NormalProjectiveSurface k)
        (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
        (b : X.toScheme ⟶ T.toScheme),
        b ≫ T.structureMorphism = X.structureMorphism →
        IsBirational b → IsIso b)
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2),
    ((∀ n : ℕ, 0 < n →
        cohomologyDimension X.structureMorphism
          (cartierDivisorModule X.toScheme (n • K)) 0 = 0) ↔
      cohomologyDimension X.structureMorphism
        (cartierDivisorModule X.toScheme (12 • K)) 0 = 0) ∧
    (cohomologyDimension X.structureMorphism
        (cartierDivisorModule X.toScheme (12 • K)) 0 = 0 ↔
      (Scheme.BirationalOver X.structureMorphism (projectiveSpaceToSpec k 2) ∨
        ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)),
          IsIntegral C ∧ LocallyOfFiniteType c ∧ QuasiCompact c ∧ IsSeparated c ∧
          topologicalKrullDim C = 1 ∧
          (∀ y : C, RegularPoint C y) ∧
          ∃ π : X.toScheme ⟶ C,
            π ≫ c = X.structureMorphism ∧
            Function.Surjective π.base ∧
            (∀ y : C, IsClosed ({y} : Set C) →
              ∃ e : π.fiber y ≅ projectiveSpace k 1,
                e.hom ≫ projectiveSpaceToSpec k 1 =
                  π.fiberι y ≫ X.structureMorphism) ∧
            ∃ σ : C ⟶ X.toScheme, σ ≫ π = 𝟙 C))
)

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (hminimal :
    ∀ (T : NormalProjectiveSurface k)
      (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
      (b : X.toScheme ⟶ T.toScheme),
      b ≫ T.structureMorphism = X.structureMorphism →
      IsBirational b → IsIso b)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

include hClassification hX hminimal eK in
/-- The complete two-equivalence statement at arbitrary original inputs. -/
theorem full_statement :
  ((∀ n : ℕ, 0 < n →
      cohomologyDimension X.structureMorphism
        (cartierDivisorModule X.toScheme (n • K)) 0 = 0) ↔
    cohomologyDimension X.structureMorphism
      (cartierDivisorModule X.toScheme (12 • K)) 0 = 0) ∧
  (cohomologyDimension X.structureMorphism
      (cartierDivisorModule X.toScheme (12 • K)) 0 = 0 ↔
    (Scheme.BirationalOver X.structureMorphism (projectiveSpaceToSpec k 2) ∨
      ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)),
        IsIntegral C ∧ LocallyOfFiniteType c ∧ QuasiCompact c ∧ IsSeparated c ∧
        topologicalKrullDim C = 1 ∧
        (∀ y : C, RegularPoint C y) ∧
        ∃ π : X.toScheme ⟶ C,
          π ≫ c = X.structureMorphism ∧
          Function.Surjective π.base ∧
          (∀ y : C, IsClosed ({y} : Set C) →
            ∃ e : π.fiber y ≅ projectiveSpace k 1,
              e.hom ≫ projectiveSpaceToSpec k 1 =
                π.fiberι y ≫ X.structureMorphism) ∧
          ∃ σ : C ⟶ X.toScheme, σ ≫ π = 𝟙 C)) :=
  hClassification k X hX hminimal K eK

include hClassification hX hminimal eK in
/-- All original positive pluricanonical vanishings give the original full
rational-or-geometrically-ruled alternative on this same minimal surface. -/
theorem rational_or_ruled_of_positive_vanishing
    (hvanish : ∀ n : ℕ, 0 < n →
      cohomologyDimension X.structureMorphism
        (cartierDivisorModule X.toScheme (n • K)) 0 = 0) :
    Scheme.BirationalOver X.structureMorphism (projectiveSpaceToSpec k 2) ∨
      ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)),
        IsIntegral C ∧ LocallyOfFiniteType c ∧ QuasiCompact c ∧ IsSeparated c ∧
        topologicalKrullDim C = 1 ∧
        (∀ y : C, RegularPoint C y) ∧
        ∃ π : X.toScheme ⟶ C,
          π ≫ c = X.structureMorphism ∧
          Function.Surjective π.base ∧
          (∀ y : C, IsClosed ({y} : Set C) →
            ∃ e : π.fiber y ≅ projectiveSpace k 1,
              e.hom ≫ projectiveSpaceToSpec k 1 =
                π.fiberι y ≫ X.structureMorphism) ∧
          ∃ σ : C ⟶ X.toScheme, σ ≫ π = 𝟙 C := by
  have hfull := full_statement hClassification X hX hminimal K eK
  exact hfull.2.mp (hfull.1.mp hvanish)

end KltDP.Geometry.HartshorneClassificationConditional

#check @KltDP.Geometry.HartshorneClassificationConditional.full_statement
#check @KltDP.Geometry.HartshorneClassificationConditional.rational_or_ruled_of_positive_vanishing
#print axioms KltDP.Geometry.HartshorneClassificationConditional.full_statement
#print axioms KltDP.Geometry.HartshorneClassificationConditional.rational_or_ruled_of_positive_vanishing
