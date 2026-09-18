import KltDP.Geometry.ArithmeticCurveAdjunction
import KltDP.Geometry.IntegralNumericalClassGroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination

/-!
# Numerical invariants from the original section and fibre classes

The integral numerical basis is an additive equivalence with the existing
Picard quotient, with its two columns identified with the original prime
Cartier divisors. Rationalization gives the original Picard rank. The actual
canonical square follows by applying arithmetic adjunction to those two
prime curves and evaluating the integral coordinates of the same canonical
Cartier divisor. There is no numerical spanning or canonical-square premise.
-/

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SmoothCanonicalExteriorComparison
open scoped TensorProduct

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- An actual rank-two integral numerical quotient has original Picard rank two.
The rational quotient is the already proved scalar extension of this group. -/
theorem picardRank_eq_two_of_integralNumericalEquiv
    (eNum : (ℤ × ℤ) ≃+ X.IntegralNumericalClassGroup) :
    X.picardRank = 2 := by
  letI : Module.Free ℤ X.IntegralNumericalClassGroup :=
    Module.Free.of_equiv eNum.toIntLinearEquiv
  change Module.finrank ℚ X.NumericalClassGroup = 2
  calc
    _ = Module.finrank ℚ (ℚ ⊗[ℤ] X.IntegralNumericalClassGroup) :=
      X.integralNumericalTensorRationalEquiv.finrank_eq.symm
    _ = Module.finrank ℤ X.IntegralNumericalClassGroup := Module.finrank_baseChange
    _ = Module.finrank ℤ (ℤ × ℤ) := eNum.toIntLinearEquiv.finrank_eq.symm
    _ = 2 := by simp

variable [IsAlgClosed k]
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Coordinates in the original integral numerical quotient preserve the
original integer pairing with every actual Cartier divisor. -/
theorem intersectionPairing_eq_of_integralNumerical_coordinates
    (A B D E : CartierDivisor X.toScheme) (n m : ℤ)
    (h : X.picardIntegralNumericalMap (cartierPicardHom X.toScheme D) =
      n • X.picardIntegralNumericalMap (cartierPicardHom X.toScheme A) +
        m • X.picardIntegralNumericalMap (cartierPicardHom X.toScheme B)) :
    X.intersectionPairing hregular D E =
      n * X.intersectionPairing hregular A E +
        m * X.intersectionPairing hregular B E := by
  have hq := congrArg
    (fun c : X.IntegralNumericalClassGroup =>
      X.numericalIntersectionBilinForm hregular
        (X.integralNumericalRationalization c)
        (X.picardNumericalMap (cartierPicardHom X.toScheme E))) h
  simp only [map_add, map_zsmul, X.integralNumericalRationalization_picard,
    LinearMap.add_apply, LinearMap.smul_apply,
    X.numericalIntersectionBilinForm_picard, cartierPicardHom_apply,
    toMul_ofMul, X.picardPairing_class, zsmul_eq_mul] at hq
  exact_mod_cast hq

/-- Two actual prime curves forming the stated integral numerical basis,
with section-fibre pairing and genus-zero fibre, determine the square of
every actual canonical Cartier representative by arithmetic adjunction. -/
theorem canonical_square_of_ruled_integralNumericalBasis
    (S0 F : X.PrimeCurve)
    (eNum : (ℤ × ℤ) ≃+ X.IntegralNumericalClassGroup)
    (heNum : ∀ n m : ℤ, eNum (n, m) =
      n • X.picardIntegralNumericalMap
        (cartierPicardHom X.toScheme (X.primeCurveCartier hregular S0)) +
      m • X.picardIntegralNumericalMap
        (cartierPicardHom X.toScheme (X.primeCurveCartier hregular F)))
    (hSF : X.intersectionPairing hregular
      (X.primeCurveCartier hregular S0) (X.primeCurveCartier hregular F) = 1)
    (hFF : X.intersectionPairing hregular
      (X.primeCurveCartier hregular F) (X.primeCurveCartier hregular F) = 0)
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (hFgenus : CurveCanonical.genus F.toSpec = 0) :
    X.intersectionPairing hregular K K =
      8 * (1 - (CurveCanonical.genus S0.toSpec : ℤ)) := by
  let DS : CartierDivisor X.toScheme := X.primeCurveCartier hregular S0
  let DF : CartierDivisor X.toScheme := X.primeCurveCartier hregular F
  obtain ⟨⟨n, m⟩, hnm⟩ := eNum.surjective
    (X.picardIntegralNumericalMap (cartierPicardHom X.toScheme K))
  have hcoord : X.picardIntegralNumericalMap (cartierPicardHom X.toScheme K) =
      n • X.picardIntegralNumericalMap (cartierPicardHom X.toScheme DS) +
        m • X.picardIntegralNumericalMap (cartierPicardHom X.toScheme DF) :=
    hnm.symm.trans (heNum n m)
  have hrowF := X.arithmetic_canonical_row hregular K eK F
  change F.intersectionNumber K + F.intersectionNumber DF =
    2 * (CurveCanonical.genus F.toSpec : ℤ) - 2 at hrowF
  rw [← X.intersectionPairing_primeCurve hregular K F,
    ← X.intersectionPairing_primeCurve hregular DF F, hFF, hFgenus] at hrowF
  have hKF : X.intersectionPairing hregular K DF = -2 := by simpa using hrowF
  have hn : n = -2 := by
    have h := X.intersectionPairing_eq_of_integralNumerical_coordinates hregular
      DS DF K DF n m hcoord
    rw [hKF, hSF, hFF] at h
    omega
  have hrowS := X.arithmetic_canonical_row hregular K eK S0
  change S0.intersectionNumber K + S0.intersectionNumber DS =
    2 * (CurveCanonical.genus S0.toSpec : ℤ) - 2 at hrowS
  rw [← X.intersectionPairing_primeCurve hregular K S0,
    ← X.intersectionPairing_primeCurve hregular DS S0] at hrowS
  change X.intersectionPairing hregular K DS +
    X.intersectionPairing hregular DS DS =
      2 * (CurveCanonical.genus S0.toSpec : ℤ) - 2 at hrowS
  have hFS : X.intersectionPairing hregular DF DS = 1 :=
    (X.intersectionPairing_symm hregular DF DS).trans hSF
  have hFK : X.intersectionPairing hregular DF K = -2 :=
    (X.intersectionPairing_symm hregular DF K).trans hKF
  have hKS := X.intersectionPairing_eq_of_integralNumerical_coordinates hregular
    DS DF K DS n m hcoord
  have hKK := X.intersectionPairing_eq_of_integralNumerical_coordinates hregular
    DS DF K K n m hcoord
  rw [hn, hFS] at hKS
  rw [hn, X.intersectionPairing_symm hregular DS K, hFK] at hKK
  linear_combination -4 * hrowS + 2 * hKS + hKK

/-- The original rank, canonical square, and their sum are conclusions of
the original integral section-fibre basis and the fibre's actual genus. -/
theorem ruled_invariants_of_integralNumericalBasis
    (S0 F : X.PrimeCurve)
    (eNum : (ℤ × ℤ) ≃+ X.IntegralNumericalClassGroup)
    (heNum : ∀ n m : ℤ, eNum (n, m) =
      n • X.picardIntegralNumericalMap
        (cartierPicardHom X.toScheme (X.primeCurveCartier hregular S0)) +
      m • X.picardIntegralNumericalMap
        (cartierPicardHom X.toScheme (X.primeCurveCartier hregular F)))
    (hSF : X.intersectionPairing hregular
      (X.primeCurveCartier hregular S0) (X.primeCurveCartier hregular F) = 1)
    (hFF : X.intersectionPairing hregular
      (X.primeCurveCartier hregular F) (X.primeCurveCartier hregular F) = 0)
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (hFgenus : CurveCanonical.genus F.toSpec = 0) :
    X.picardRank = 2 ∧
      X.intersectionPairing hregular K K =
        8 * (1 - (CurveCanonical.genus S0.toSpec : ℤ)) ∧
      X.intersectionPairing hregular K K + (X.picardRank : ℤ) =
        10 - 8 * (CurveCanonical.genus S0.toSpec : ℤ) := by
  have hrank := X.picardRank_eq_two_of_integralNumericalEquiv eNum
  have hsquare := X.canonical_square_of_ruled_integralNumericalBasis hregular
    S0 F eNum heNum hSF hFF K eK hFgenus
  refine ⟨hrank, hsquare, ?_⟩
  rw [hrank, hsquare]
  omega

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.picardRank_eq_two_of_integralNumericalEquiv
#print axioms KltDP.Geometry.NormalProjectiveSurface.picardRank_eq_two_of_integralNumericalEquiv
#check @KltDP.Geometry.NormalProjectiveSurface.intersectionPairing_eq_of_integralNumerical_coordinates
#print axioms KltDP.Geometry.NormalProjectiveSurface.intersectionPairing_eq_of_integralNumerical_coordinates
#check @KltDP.Geometry.NormalProjectiveSurface.canonical_square_of_ruled_integralNumericalBasis
#print axioms KltDP.Geometry.NormalProjectiveSurface.canonical_square_of_ruled_integralNumericalBasis
#check @KltDP.Geometry.NormalProjectiveSurface.ruled_invariants_of_integralNumericalBasis
#print axioms KltDP.Geometry.NormalProjectiveSurface.ruled_invariants_of_integralNumericalBasis
