import KltDP.Geometry.AffineBlowupRegularPairExceptionalDVR

/-!
# Identification of an actual exceptional prime on a regular-pair chart

The original extended centre is a nonzero prime ideal. At an actual
codimension-one stalk, its nonzero prime extension is the DVR maximal
ideal. Prime localization contracts it back, identifying the original
prime with the original extended centre. No equality of these ideals is
assumed.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)
variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)}) [I.IsPrime]

include ha hb hI in
/-- The actual exceptional generic prime lies over the original centre. -/
theorem chartCenterIdeal_comap_baseMap :
    (chartCenterIdeal I a).comap (chartBaseMap I a) = I := by
  ext r
  rw [← exceptionalCoordinateMap_ker I a b ha hb hI]
  change exceptionalCoordinateMap I a b ha hb hI (chartBaseMap I a r) = 0 ↔ r ∈ I
  rw [exceptionalCoordinateMap_baseMap, Polynomial.C_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem]

variable [IsDomain R]

local instance : IsDomain (chartRing I a) := chartRing_isDomain_of_parameter I a ha

include ha hb hI in
/-- On a regular-pair chart, an actual DVR prime above the centre is
exactly the original exceptional chart prime. The DVR input is intended
to be supplied by the original global prime-curve stalk equivalence. -/
theorem prime_eq_chartCenterIdeal (P : Ideal (chartRing I a)) [P.IsPrime] :
    letI : IsDomain (chartRing I a) := chartRing_isDomain_of_parameter I a ha
    letI : IsDomain (Localization.AtPrime P) := inferInstance
    ∀ [IsDiscreteValuationRing (Localization.AtPrime P)],
      I ≤ P.comap (chartBaseMap I a) → P = chartCenterIdeal I a := by
  letI : IsDomain (chartRing I a) := chartRing_isDomain_of_parameter I a ha
  letI : IsDomain (Localization.AtPrime P) := inferInstance
  intro hDVR hIP
  let J := chartCenterIdeal I a
  let L := Localization.AtPrime P
  letI : J.IsPrime := chartCenterIdeal_isPrime I a b ha hb hI
  have hJP : J ≤ P := Ideal.map_le_iff_le_comap.mpr hIP
  let Q := J.map (algebraMap (chartRing I a) L)
  have hQprime : Q.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime P hJP
  have hQne : Q ≠ ⊥ := by
    intro hQ
    have hz : algebraMap (chartRing I a) L (chartBaseMap I a (a : R)) ∈ Q :=
      Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ a.property)
    have hzero : algebraMap (chartRing I a) L (chartBaseMap I a (a : R)) = 0 := by
      simpa only [hQ, Ideal.mem_bot] using hz
    exact (nonZeroDivisors.coe_ne_zero
      ⟨_, IsLocalization.nonZeroDivisors_le_comap P.primeCompl L
        (chartBaseMap_equation_mem_nonZeroDivisors I a)⟩) hzero
  have hQmax : Q = IsLocalRing.maximalIdeal L :=
    IsLocalRing.eq_maximalIdeal (hQprime.isMaximal hQne)
  have hcontract : Q.comap (algebraMap (chartRing I a) L) = J :=
    Ideal.under_map_of_isLocalizationAtPrime P hJP
  calc
    P = (IsLocalRing.maximalIdeal L).comap (algebraMap (chartRing I a) L) :=
      Localization.AtPrime.comap_maximalIdeal.symm
    _ = Q.comap (algebraMap (chartRing I a) L) := congrArg _ hQmax.symm
    _ = chartCenterIdeal I a := hcontract

end KltDP.Geometry.AffineBlowupRegularPairChart
