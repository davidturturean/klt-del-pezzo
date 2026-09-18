import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback
import KltDP.Geometry.NormalFiniteTypeValuationPoint

/-!
# Actual local canonical frames on arbitrary normal models

A frame consists of an actual smooth open immersion and a point over the original point,
an actual Cartier representative of the top differential sheaf and an
original Cartier equation chart through that point. Normalization compares
its rational coordinate with a fixed target reference on a nonempty common
open. The common open need not contain the original divisorial point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelCanonical

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] {V : Scheme.{u}} [IsIntegral V]

/-- Actual local top-differential data through the original model point.
No order, discrepancy, bound or comparison-model conclusion is a field. -/
structure LocalFrame (σ : V ⟶ Spec (CommRingCat.of k)) (x : V) where
  neighborhood : Scheme.{u}
  toModel : neighborhood ⟶ V
  isOpenImmersion : IsOpenImmersion toModel
  point : neighborhood
  point_eq : toModel.base point = x
  smooth : IsSmoothOfRelativeDimension 2 (toModel ≫ σ)
  divisor :
    letI : Nonempty neighborhood := ⟨point⟩
    letI : IsOpenImmersion toModel := isOpenImmersion
    letI : IsIntegral neighborhood := isIntegral_of_isOpenImmersion toModel
    CartierDivisor neighborhood
  canonicalIso :
    letI : Nonempty neighborhood := ⟨point⟩
    letI : IsOpenImmersion toModel := isOpenImmersion
    letI : IsIntegral neighborhood := isIntegral_of_isOpenImmersion toModel
    cartierDivisorModule neighborhood divisor ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior (toModel ≫ σ) 2
  equationChart :
    letI : Nonempty neighborhood := ⟨point⟩
    letI : IsOpenImmersion toModel := isOpenImmersion
    letI : IsIntegral neighborhood := isIntegral_of_isOpenImmersion toModel
    CartierEquationChart neighborhood divisor
  point_mem_equation :
    letI : Nonempty neighborhood := ⟨point⟩
    letI : IsOpenImmersion toModel := isOpenImmersion
    letI : IsIntegral neighborhood := isIntegral_of_isOpenImmersion toModel
    point ∈ equationChart.openSet

namespace LocalFrame

variable {σ : V ⟶ Spec (CommRingCat.of k)} {x : V} (F : LocalFrame σ x)

instance neighborhood_nonempty : Nonempty F.neighborhood := ⟨F.point⟩

instance toModel_isOpenImmersion : IsOpenImmersion F.toModel := F.isOpenImmersion

instance neighborhood_isIntegral : IsIntegral F.neighborhood :=
  isIntegral_of_isOpenImmersion F.toModel

/-- The original local equation in the original model function field,
transported by the actual open-immersion function-field isomorphism. -/
def equationOnModel : V.functionFieldˣ :=
  Units.map (OpenImmersionRational.functionFieldIso F.toModel).inv.hom.toMonoidHom
    F.equationChart.equation

/-- Canonical order at the original model DVR, using that same local equation. -/
def order [IsDiscreteValuationRing (V.presheaf.stalk x)] : ℤ :=
  stalkDivisorOrder V x F.equationOnModel

end LocalFrame

section Normalization

variable (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme]

local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- The same rational top-form coordinate on an actual nonempty common
open, with both original maps over X and their actual exterior differentials. -/
def IsNormalized
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    (v : V ⟶ X.toScheme) (x : V)
    (F : LocalFrame (v ≫ X.structureMorphism) x) : Prop :=
  ∃ (Z : F.neighborhood.Opens) (hne : Nonempty Z.toScheme),
    letI : Nonempty Z.toScheme := hne
    letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
    ∃ (j : Z.toScheme ⟶ U.toScheme) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      letI : GenericPointPreserving j := ⟨genericPoint_eq_of_isOpenImmersion j⟩
      letI : GenericPointPreserving Z.ι := ⟨genericPoint_eq_of_isOpenImmersion Z.ι⟩
      ∃ htriangle : j ≫ U.ι = (Z.ι ≫ F.toModel) ≫ v,
        let σZ := Z.ι ≫ (F.toModel ≫ (v ≫ X.structureMorphism))
        let hbase : j ≫ (U.ι ≫ X.structureMorphism) = σZ := by
          simpa only [Category.assoc] using
            congrArg (fun f => f ≫ X.structureMorphism) htriangle
        CartierRationalCoordinate.coordinate Z.toScheme
            (DominantCartierPullback.pullbackHom Z.ι F.divisor)
            (SmoothCanonicalExteriorComparison.relativeDifferentialExterior σZ 2)
            (CartierRationalCoordinate.canonicalOpenPullbackIso Z.ι
              (F.toModel ≫ (v ≫ X.structureMorphism)) σZ rfl
              F.divisor F.canonicalIso) =
          CartierRationalCoordinate.coordinate Z.toScheme
            (DominantCartierPullback.pullbackHom j KU)
            (SmoothCanonicalExteriorComparison.relativeDifferentialExterior σZ 2)
            (CartierRationalCoordinate.canonicalOpenPullbackIso j
              (U.ι ≫ X.structureMorphism) σZ hbase KU eKU)

end Normalization

/-- The literal discrepancy coefficient for an actual Cartier numerator.
Positivity and numerator equality are supplied by the all-model predicate,
which quantifies every such numerator and does not fix a Cartier index. -/
def discrepancyForCartierMultiple (X : NormalProjectiveSurface k)
    (v : V ⟶ X.toScheme) [GenericPointPreserving v] (x : V)
    [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (F : LocalFrame (v ≫ X.structureMorphism) x)
    (n : ℕ) (A : CartierDivisor X.toScheme) : ℚ :=
  (F.order : ℚ) -
    (cartierOrderAt V (DominantCartierPullback.pullbackHom v A) x : ℚ) / (n : ℚ)

end KltDP.Geometry.NormalModelCanonical

#check @KltDP.Geometry.NormalModelCanonical.LocalFrame
#check @KltDP.Geometry.NormalModelCanonical.IsNormalized
#check @KltDP.Geometry.NormalModelCanonical.discrepancyForCartierMultiple
