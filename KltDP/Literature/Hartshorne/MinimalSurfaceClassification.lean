import KltDP.Geometry.Resolution
import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Compatibility.BirationalRationality
import Mathlib.AlgebraicGeometry.Fiber

/-! Full published Hartshorne V.6.1 on the original objects.
Isolated candidate bound by ROOT_SCOPE_DECISION and ROOT_CANDIDATE_SOURCE_DECISION.
No production registry activation is performed by this file. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory KltDP.Geometry
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Literature.Hartshorne

axiom minimal_surface_classification_literal :
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

end KltDP.Literature.Hartshorne

#check @KltDP.Literature.Hartshorne.minimal_surface_classification_literal
#print axioms KltDP.Literature.Hartshorne.minimal_surface_classification_literal
