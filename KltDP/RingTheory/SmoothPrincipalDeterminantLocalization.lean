import KltDP.RingTheory.SmoothPrincipalDeterminantRestriction
import Mathlib.RingTheory.Localization.Ideal

/-!
# Determinant adjunction on an original principal localization

Localization supplies the actual image ideal, regular image equation,
and standard-smooth quotient chart. Thus the determinant restriction law
requires only the original smooth chart and its original regular equation.
The scalar action on the localized quotient is the original quotient map.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.RingTheory.SmoothPrincipalDeterminantLocalization

open SmoothPrincipalDeterminantRestriction

variable (R A A' : Type u) [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
  (J : Ideal A) (r : A) [IsLocalization.Away r A']

/-- The original ideal extended to the original principal localization. -/
abbrev localizedIdeal : Ideal A' := J.map (algebraMap A A')

private theorem idealLe : J ≤ (localizedIdeal A A' J).comap (algebraMap A A') :=
  fun _ hx => Ideal.mem_map_of_mem _ hx

local instance quotientAlgebra : Algebra (A ⧸ J) (A' ⧸ localizedIdeal A A' J) :=
  (quotientMap A A' J (localizedIdeal A A' J) (idealLe A A' J)).toAlgebra

local instance quotientTowerA : IsScalarTower A (A ⧸ J) (A' ⧸ localizedIdeal A A' J) :=
  quotientMapTowerA A A' J (localizedIdeal A A' J) (idealLe A A' J)

local instance quotientTowerR : IsScalarTower R (A ⧸ J) (A' ⧸ localizedIdeal A A' J) :=
  quotientMapTowerR R A A' J (localizedIdeal A A' J) (idealLe A A' J)

/-- The original quotient of the localization is localization of the original quotient.
This is the pinned surjective-square localization theorem on the two quotient maps. -/
theorem quotient_isLocalization :
    IsLocalization.Away (Ideal.Quotient.mk J r) (A' ⧸ localizedIdeal A A' J) := by
  simp only [IsLocalization.Away, ← Submonoid.map_powers]
  refine IsLocalization.of_surjective (Submonoid.powers r) A'
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (localizedIdeal A A' J)) Ideal.Quotient.mk_surjective ?_ ?_
  · apply RingHom.ext
    intro a
    change Ideal.Quotient.mk (localizedIdeal A A' J) (algebraMap A A' a) =
      quotientMap A A' J (localizedIdeal A A' J) (idealLe A A' J) (Ideal.Quotient.mk J a)
    exact (Ideal.quotientMap_mk (J := J) (I := localizedIdeal A A' J)
      (f := algebraMap A A') (H := idealLe A A' J) (x := a)).symm
  · simp only [Ideal.mk_ker, localizedIdeal, le_refl]

local instance localizedQuotient :
    IsLocalization.Away (Ideal.Quotient.mk J r) (A' ⧸ localizedIdeal A A' J) :=
  quotient_isLocalization A A' J r

variable [Algebra.FormallySmooth R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]

include r in
/-- The original ambient localization remains formally smooth over the original base. -/
theorem ambientFormallySmooth : Algebra.FormallySmooth R A' := by
  letI : Algebra.FormallySmooth A A' := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers r)
  exact Algebra.FormallySmooth.comp R A A'

include r in
/-- The original localized quotient retains relative dimension one. -/
theorem quotient_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ localizedIdeal A A' J) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0
      (A ⧸ J) (A' ⧸ localizedIdeal A A' J) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (Ideal.Quotient.mk J r)
  simpa only [Nat.zero_add] using
    (Algebra.IsStandardSmoothOfRelativeDimension.trans R (A ⧸ J)
      (A' ⧸ localizedIdeal A A' J) (n := 1) (m := 0))

variable (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)

include hJ in
/-- The original image equation generates the original extended ideal. -/
theorem mappedEquation_span :
    Ideal.span {(mappedEquation A A' J (localizedIdeal A A' J) (idealLe A A' J) d : A')} =
      localizedIdeal A A' J := by
  change Ideal.span {algebraMap A A' (d : A)} = J.map (algebraMap A A')
  simpa only [Ideal.map_span, Set.image_singleton] using
    congrArg (Ideal.map (algebraMap A A')) hJ

include r hd in
/-- The same original image equation is regular by the pinned localization theorem. -/
theorem mappedEquation_regular :
    (mappedEquation A A' J (localizedIdeal A A' J) (idealLe A A' J) d : A') ∈
      nonZeroDivisors A' :=
  IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r) A' hd

/-- Actual determinant adjunction commutes with localization without additional
smaller-equation, smoothness, or determinant-compatibility hypotheses. -/
theorem determinantEquiv_localization (n : KaehlerDifferential R (A ⧸ J)) :
    letI : Algebra.FormallySmooth R A' := ambientFormallySmooth R A A' r
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ localizedIdeal A A' J) :=
      quotient_standardSmooth R A A' J r
    KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map
        (quotientMap A A' J (localizedIdeal A A' J) (idealLe A A' J)) 2
        (ambientTensorMap R A A' J (localizedIdeal A A' J) (idealLe A A' J))
        (SmoothPrincipalConormalDeterminant.determinantEquiv R A J d hJ hd n) =
      SmoothPrincipalConormalDeterminant.determinantEquiv R A' (localizedIdeal A A' J)
        (mappedEquation A A' J (localizedIdeal A A' J) (idealLe A A' J) d)
        (mappedEquation_span A A' J d hJ) (mappedEquation_regular A A' J r d hd)
        (quotientDifferentialMap R A A' J (localizedIdeal A A' J) (idealLe A A' J) n) := by
  letI : Algebra.FormallySmooth R A' := ambientFormallySmooth R A A' r
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ localizedIdeal A A' J) :=
    quotient_standardSmooth R A A' J r
  exact determinantEquiv_restriction R A A' J (localizedIdeal A A' J) (idealLe A A' J)
    d hJ hd (mappedEquation_span A A' J d hJ) (mappedEquation_regular A A' J r d hd) n

end KltDP.RingTheory.SmoothPrincipalDeterminantLocalization
