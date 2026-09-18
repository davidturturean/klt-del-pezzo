import KltDP.Geometry.IntegralNumericalClassGroup
import KltDP.Geometry.SchemePicardPullback
import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import Mathlib.AlgebraicGeometry.Fiber

/-! Full published Hartshorne V.2.5 on the original objects.
Isolated candidate bound by ROOT_SCOPE_DECISION and ROOT_CANDIDATE_SOURCE_DECISION.
No production registry activation is performed by this file. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory KltDP.Geometry
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Literature.Hartshorne

axiom ruled_surface_genus_literal :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    (hCdim : topologicalKrullDim C = 1)
    (hCreg : ∀ y : C, RegularPoint C y)
    (π : X.toScheme ⟶ C)
    (hbase : π ≫ c = X.structureMorphism)
    (hsurj : Function.Surjective π.base)
    (hfib : ∀ y : C, IsClosed ({y} : Set C) →
      ∃ e : π.fiber y ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 =
          π.fiberι y ≫ X.structureMorphism)
    (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C),
    (eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) - 1 =
      -(CurveCanonical.genus c : ℤ)) ∧
    (cohomologyDimension X.structureMorphism
        (relativeDifferentialExterior X.structureMorphism 2) 0 = 0) ∧
    (cohomologyDimension X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 =
      CurveCanonical.genus c)

end KltDP.Literature.Hartshorne

#check @KltDP.Literature.Hartshorne.ruled_surface_genus_literal
#print axioms KltDP.Literature.Hartshorne.ruled_surface_genus_literal
