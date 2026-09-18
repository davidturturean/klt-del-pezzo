import KltDP.Geometry.CartierSectionMonomialIndependence
import KltDP.Geometry.ProperInvertibleSectionBasis
import KltDP.Geometry.Positivity
import KltDP.Geometry.CartierPicardHom
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Actual H0 bounds from independent original Cartier section ratios

The original monomial sections are linearly independent under the original
base-field action. Properness supplies finite dimension of the original
section space. Its dimension therefore dominates the actual box cardinality.
The existing Cartier-Picard homomorphism identifies this with H0 of the
original Picard power, without replacing the line bundle or its scalar action.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.SectionRatioHZero

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SectionMonomialGrowth

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
  (f : X ⟶ Spec (CommRingCat.of k))

/-- H0 of the original Cartier multiple is H0 of the original Picard power. -/
theorem cohomologyDimension_eq_picard_power (D : CartierDivisor X) (n : ℕ) :
    cohomologyDimension f (cartierDivisorModule X (n • D)) 0 =
      Positivity.picardHZero f ((cartierDivisorInvertibleSheaf X D).toPic ^ n) := by
  have hclass : cartierPicardClass X (n • D) = cartierPicardClass X D ^ n :=
    congrArg Additive.toMul ((cartierPicardHom X).map_nsmul D n)
  change cohomologyDimension f (cartierDivisorModule X (n • D)) 0 =
    Positivity.picardHZero f (cartierPicardClass X D ^ n)
  rw [← hclass]
  exact (Positivity.picardHZero_toPic f (cartierDivisorInvertibleSheaf X (n • D))).symm

variable [IsProper f]

/-- Independent original ratios give the box lower bound for actual H0. -/
theorem box_cohomologyDimension_lowerBound (D : CartierDivisor X)
    (s₀ : sections (cartierDivisorModule X D)) (hs₀ : s₀ ≠ 0) {d : ℕ}
    (s : Fin d → sections (cartierDivisorModule X D))
    (hs : letI := functionFieldAlgebra f
      AlgebraicIndependent k (fun i => cartierGlobalSectionRationalValue X D (s i) /
        cartierGlobalSectionRationalValue X D s₀)) (q : ℕ) :
    (q + 1) ^ d ≤ cohomologyDimension f (cartierDivisorModule X ((q * d) • D)) 0 := by
  letI := baseSectionsModule f (cartierDivisorModule X ((q * d) • D))
  letI : FiniteDimensional k (sections (cartierDivisorModule X ((q * d) • D))) :=
    CompleteLinearSystemSections.topSections_finiteDimensional f
      (cartierDivisorInvertibleSheaf X ((q * d) • D))
  change (q + 1) ^ d ≤ CompleteLinearSystemSections.dimension f
    (cartierDivisorInvertibleSheaf X ((q * d) • D))
  rw [CompleteLinearSystemSections.dimension_eq_finrank_topSections]
  have h := (boxSection_linearIndependent f D s₀ hs₀ s hs q).fintype_card_le_finrank
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

/-- The same bound concerns the unchanged Picard H0 of the original power. -/
theorem box_picardHZero_lowerBound (D : CartierDivisor X)
    (s₀ : sections (cartierDivisorModule X D)) (hs₀ : s₀ ≠ 0) {d : ℕ}
    (s : Fin d → sections (cartierDivisorModule X D))
    (hs : letI := functionFieldAlgebra f
      AlgebraicIndependent k (fun i => cartierGlobalSectionRationalValue X D (s i) /
        cartierGlobalSectionRationalValue X D s₀)) (q : ℕ) :
    (q + 1) ^ d ≤ Positivity.picardHZero f
      ((cartierDivisorInvertibleSheaf X D).toPic ^ (q * d)) := by
  rw [← cohomologyDimension_eq_picard_power f D (q * d)]
  exact box_cohomologyDimension_lowerBound f D s₀ hs₀ s hs q

end KltDP.Geometry.SectionRatioHZero
