import KltDP.Geometry.BirationalAdapters
import KltDP.Geometry.NormalModelCanonicalFrame
import KltDP.Geometry.CanonicalWeilDivisor
import KltDP.Geometry.CartierPicardEndpointRational

/-!
# The all-normal-model KLT predicate for the zero boundary

The target canonical divisor is fixed as an actual integral Weil divisor.
Every original normal integral locally finite-type birational model and
every original codimension-one point is tested. Normalized local canonical
frames must exist; every such frame and every positive Cartier numerator
must give discrepancy greater than minus one. Models need not be proper,
projective or smooth. This definition proves no KLT assertion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

open NormalProjectiveSurface NormalModelCanonical

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- All ordinary discrepancies for a fixed genuine target canonical divisor.
The explicit frame-existence clause prevents an empty normalized family
from satisfying the coefficient test. Canonical reference choices and all
positive Cartier numerators are universally quantified. -/
def IsKltWithCanonicalDivisor (X : NormalProjectiveSurface k) (KX : X.WeilDivisor) : Prop :=
  IsCanonicalWeilDivisor X KX ∧
    X.QCartier (rationalizeWeilDivisor X KX) ∧
    ∀ (U : X.toScheme.Opens) (hne : Nonempty U.toScheme),
      letI : Nonempty U.toScheme := hne
      letI : Nonempty U := ⟨Classical.choice hne⟩
      letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
      IsSmoothOfRelativeDimension 2 (U.ι ≫ X.structureMorphism) →
      (∀ C : X.PrimeCurve, C.genericPoint ∈ U) →
      ∀ (KU : CartierDivisor U.toScheme)
        (eKU : cartierDivisorModule U.toScheme KU ≅
          SmoothCanonicalExteriorComparison.relativeDifferentialExterior
            (U.ι ≫ X.structureMorphism) 2),
        OpenCartierWeil.restrictedWeilHom U KU = KX →
        ∀ (V : Scheme.{u}) [IsIntegral V] (hnormal : IsNormalScheme V)
          (v : V ⟶ X.toScheme) [LocallyOfFiniteType (v ≫ X.structureMorphism)]
          (hv : IsBirationalScheme v) (x : CodimensionOnePoint V),
          letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
          letI : IsDiscreteValuationRing (V.presheaf.stalk x.val) :=
            normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
          (∃ F : LocalFrame (v ≫ X.structureMorphism) x.val,
            IsNormalized X U KU eKU v x.val F) ∧
          ∀ F : LocalFrame (v ≫ X.structureMorphism) x.val,
            IsNormalized X U KU eKU v x.val F →
            ∀ (n : ℕ), 0 < n → ∀ A : CartierDivisor X.toScheme,
              rationalizeWeilDivisor X (X.cartierToWeilHom A) =
                n • rationalizeWeilDivisor X KX →
              (-1 : ℚ) < discrepancyForCartierMultiple X v x.val F n A

/-- Kawamata log terminal singularities for the zero-boundary normal
projective surface, using actual divisors on all normal birational models. -/
def IsKlt (X : NormalProjectiveSurface k) : Prop :=
  ∃ KX : X.WeilDivisor, IsKltWithCanonicalDivisor X KX

end KltDP.Geometry

#check @KltDP.Geometry.IsKltWithCanonicalDivisor
#check @KltDP.Geometry.IsKlt
