import KltDP.Examples.FrobeniusSquareGenericMap
import KltDP.Examples.FrobeniusSquareRationalMap
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The original projective generic map is the square fraction map

The actual polynomial open chart identifies the projective function field
with the affine generic stalk, and the fraction-field universal property
identifies that stalk with `RatFunc k`. The existing chart equation and
the original stalk map on coefficients prove the square-map comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusSquareGenericMap

open KltDP.Geometry ProjectiveLineComparison FrobeniusProjectiveMorphism
  FrobeniusGlobalGraphCompatibility FrobeniusSquareRationalMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k : Type u) [Field k]

local instance comparisonLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance comparisonPolynomialAlgebra :
    Algebra (Polynomial k) (Spec (CommRingCat.of (Polynomial k))).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial k))

local instance comparisonPolynomialFractionRing :
    IsFractionRing (Polynomial k) (Spec (CommRingCat.of (Polynomial k))).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of (Polynomial k))

local instance comparisonChartGeneric (i : Fin 2) :
    GenericPointPreserving (polynomialChartMap k i) :=
  ⟨genericPoint_eq_of_isOpenImmersion _⟩

/-- The original affine generic stalk is the fraction field of its polynomial ring. -/
def affineFieldEquiv :
    (Spec (CommRingCat.of (Polynomial k))).functionField ≃+* RatFunc k :=
  IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl (Polynomial k))

theorem affineFieldEquiv_polynomial (p : Polynomial k) :
    affineFieldEquiv k
        (algebraMap (Polynomial k) (Spec (CommRingCat.of (Polynomial k))).functionField p) =
      algebraMap (Polynomial k) (RatFunc k) p :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (RingEquiv.refl (Polynomial k)) p

/-- The original affine function-field map is the unique extension of the square ring map. -/
theorem affineFieldMap_square :
    (affineFieldEquiv k).toRingHom.comp
        (functionFieldMap (Spec.map (CommRingCat.ofHom
          (polynomialPowerHom (k := k) 2)))).hom =
      (squareHom k).toRingHom.comp (affineFieldEquiv k).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Polynomial k)
  intro p
  change affineFieldEquiv k
      (functionFieldMap (Spec.map (CommRingCat.ofHom (polynomialPowerHom 2)))
        (algebraMap (Polynomial k) (Spec (CommRingCat.of (Polynomial k))).functionField p)) =
    squareHom k (affineFieldEquiv k
      (algebraMap (Polynomial k) (Spec (CommRingCat.of (Polynomial k))).functionField p))
  have hp : functionFieldMap
      (Spec.map (CommRingCat.ofHom (polynomialPowerHom (k := k) 2)))
      (algebraMap (Polynomial k) (Spec (CommRingCat.of (Polynomial k))).functionField p) =
    algebraMap (Polynomial k) (Spec (CommRingCat.of (Polynomial k))).functionField
      (polynomialPowerHom 2 p) :=
    SpecFunctionFieldMap.map_algebraMap
      (CommRingCat.ofHom (polynomialPowerHom (k := k) 2)) p
  rw [hp, affineFieldEquiv_polynomial,
    affineFieldEquiv_polynomial, squareHom_polynomial]

/-- The comparison retains the original projective polynomial chart. -/
def projectiveFieldEquiv : (projectiveSpace k 1).functionField ≃+* RatFunc k :=
  (OpenImmersionRational.functionFieldIso (polynomialChartMap k 0)).commRingCatIsoToRingEquiv.trans
    (affineFieldEquiv k)

/-- Conjugacy for the original projective generic stalk map, with no map-identification premise. -/
theorem projectiveFieldMap_square (z : (projectiveSpace k 1).functionField) :
    projectiveFieldEquiv k (functionFieldMap (projectivePowerMorphism (k := k) 2) z) =
      squareHom k (projectiveFieldEquiv k z) := by
  have h := ConcreteCategory.congr_hom (functionFieldMap_chart k 0) z
  change functionFieldMap (polynomialChartMap k 0)
      (functionFieldMap (projectivePowerMorphism (k := k) 2) z) =
    functionFieldMap (Spec.map (CommRingCat.ofHom (polynomialPowerHom 2)))
      (functionFieldMap (polynomialChartMap k 0) z) at h
  change affineFieldEquiv k (functionFieldMap (polynomialChartMap k 0)
      (functionFieldMap (projectivePowerMorphism (k := k) 2) z)) =
    squareHom k (affineFieldEquiv k (functionFieldMap (polynomialChartMap k 0) z))
  rw [h]
  exact RingHom.congr_fun (affineFieldMap_square k)
    (functionFieldMap (polynomialChartMap k 0) z)

end KltDP.Examples.FrobeniusSquareGenericMap
