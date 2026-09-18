import KltDP.Geometry.IntegralNumericalClassGroup
import KltDP.Geometry.SchemePicardPullback
import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import Mathlib.AlgebraicGeometry.Fiber

/-! Full published Hartshorne V.2.3 on the original objects.
Isolated candidate bound by ROOT_SCOPE_DECISION and ROOT_CANDIDATE_SOURCE_DECISION.
No production registry activation is performed by this file. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory KltDP.Geometry
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Literature.Hartshorne

axiom ruled_surface_picard_literal :
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
    (σ : C ⟶ X.toScheme) (hσ : σ ≫ π = 𝟙 C)
    (S₀ : X.PrimeCurve) (e₀ : S₀.toScheme ≅ C)
    (he₀ : e₀.inv ≫ S₀.inclusion = σ)
    (y : C) (hy : IsClosed ({y} : Set C))
    (F : X.PrimeCurve) (eF : F.toScheme ≅ π.fiber y)
    (heF : eF.hom ≫ π.fiberι y = F.inclusion),
    let DS := X.primeCurveCartier hX S₀
    let DF := X.primeCurveCartier hX F
    let PS := cartierPicardHom X.toScheme DS
    let PF := cartierPicardHom X.toScheme DF
    ∃ ePic : (ℤ × Additive C.Pic) ≃+ Additive X.toScheme.Pic,
      ∃ eNum : (ℤ × ℤ) ≃+ X.IntegralNumericalClassGroup,
        (∀ (n : ℤ) (L : Additive C.Pic),
          ePic (n, L) = n • PS + (schemePicardPullbackHom π).toAdditive L) ∧
        (∀ n m : ℤ,
          eNum (n, m) =
            n • X.picardIntegralNumericalMap PS +
            m • X.picardIntegralNumericalMap PF) ∧
        X.intersectionPairing hX DS DF = 1 ∧
        X.intersectionPairing hX DF DF = 0

end KltDP.Literature.Hartshorne

#check @KltDP.Literature.Hartshorne.ruled_surface_picard_literal
#print axioms KltDP.Literature.Hartshorne.ruled_surface_picard_literal
