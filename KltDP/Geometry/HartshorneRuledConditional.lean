import KltDP.Geometry.IntegralNumericalClassGroup
import KltDP.Geometry.SchemePicardPullback
import KltDP.Geometry.SmoothCurveCanonicalDegree
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import Mathlib.AlgebraicGeometry.Fiber

/-!
# The complete Hartshorne V.2.3 and V.2.5 hypotheses on original objects

Each full reviewed source statement is an explicit hypothetical parameter.
The first retains the Picard pullback decomposition, the integral numerical
quotient with both original generators and both original pairings. The
second retains all three arithmetic genus, geometric genus and H1 clauses.
No product restriction, source predicate or literature declaration is added.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u

namespace KltDP.Geometry.HartshorneRuledConditional

variable (hPicard :
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
)

variable (hGenus :
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
)

variable {k : Type u} [Field k] [IsAlgClosed k]
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

include hPicard hCdim hCreg hbase hsurj hfib hσ in
/-- The entire Picard and numerical decomposition at original section and
scheme-fibre objects, retaining the prescribed evaluation equations. -/
theorem decomposition_at
    (S₀ : X.PrimeCurve) (e₀ : S₀.toScheme ≅ C)
    (he₀ : e₀.inv ≫ S₀.inclusion = σ)
    (y : C) (hy : IsClosed ({y} : Set C))
    (F : X.PrimeCurve) (eF : F.toScheme ≅ π.fiber y)
    (heF : eF.hom ≫ π.fiberι y = F.inclusion) :
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
      X.intersectionPairing hX DF DF = 0 :=
  hPicard k X hX C c hCdim hCreg π hbase hsurj hfib σ hσ
    S₀ e₀ he₀ y hy F eF heF

include hGenus hX hCdim hCreg hbase hsurj hfib hσ in
/-- All three published genus conclusions at the same original ruled map. -/
theorem genera_at :
  (eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) - 1 =
    -(CurveCanonical.genus c : ℤ)) ∧
  (cohomologyDimension X.structureMorphism
      (relativeDifferentialExterior X.structureMorphism 2) 0 = 0) ∧
  (cohomologyDimension X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) 1 =
    CurveCanonical.genus c) :=
  hGenus k X hX C c hCdim hCreg π hbase hsurj hfib σ hσ

end KltDP.Geometry.HartshorneRuledConditional

#check @KltDP.Geometry.HartshorneRuledConditional.decomposition_at
#check @KltDP.Geometry.HartshorneRuledConditional.genera_at
#print axioms KltDP.Geometry.HartshorneRuledConditional.decomposition_at
#print axioms KltDP.Geometry.HartshorneRuledConditional.genera_at
