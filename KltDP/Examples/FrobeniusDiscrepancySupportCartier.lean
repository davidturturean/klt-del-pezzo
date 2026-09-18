import KltDP.Examples.FrobeniusDiscrepancySmoothSupport
import KltDP.Geometry.SelectedPrimeCurveCartierUnion

/-!
# Actual reduced Cartier support of the candidate discrepancy

The finite support of the original rational candidate determines the sum
of the original prime Cartier divisors, each with multiplicity one. Its
Cartier-to-Weil coefficients are computed, and its actual regular divisor
ideal is the vanishing ideal of the candidate's original geometric support.
This does not identify the rational candidate's coefficients with one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyBounds

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreGraphExceptionalPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

local instance : DecidableEq (sourceSurface q n a ha hproj).PrimeCurve := Classical.decEq _

/-- Multiplicity-one sum of the actual Cartier primes in the candidate support. -/
def candidateSupportCartier : CartierDivisor (sourceSurface q n a ha hproj).toScheme :=
  ∑ C ∈ (candidate q n a ha hproj).support,
    (sourceSurface q n a ha hproj).primeCurveCartier
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj) C

/-- The actual Cartier-to-Weil image is precisely the existing selected-prime sum. -/
theorem candidateSupportCartier_weil :
    (sourceSurface q n a ha hproj).cartierToWeilHom
        (candidateSupportCartier q n a ha hproj) =
      (sourceSurface q n a ha hproj).selectedPrimeWeil
        (candidate q n a ha hproj).support := by
  simp only [candidateSupportCartier, map_sum, cartierToWeilHom_primeCurveCartier,
    selectedPrimeWeil]

/-- Every selected original prime has multiplicity one, and every other prime zero. -/
theorem candidateSupportCartier_multiplicity
    (C : (sourceSurface q n a ha hproj).PrimeCurve) :
    (sourceSurface q n a ha hproj).cartierToWeilHom
        (candidateSupportCartier q n a ha hproj) C =
      if C ∈ (candidate q n a ha hproj).support then 1 else 0 := by
  classical
  rw [candidateSupportCartier_weil, selectedPrimeWeil_apply]

theorem candidateSupportCartier_effective :
    EffectiveDivisor ((sourceSurface q n a ha hproj).cartierToWeilHom
      (candidateSupportCartier q n a ha hproj)) := by
  rw [candidateSupportCartier_weil]
  exact (sourceSurface q n a ha hproj).selectedPrimeWeil_effective _

/-- The original Cartier support divisor has an actual regular equation cover. -/
theorem candidateSupportCartier_hasRegularEquations :
    HasRegularCartierEquations (sourceSurface q n a ha hproj).toScheme
      (candidateSupportCartier q n a ha hproj) := by
  letI := (sourceSurface q n a ha hproj).stalks_uniqueFactorizationMonoid_of_regular
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
  exact (sourceSurface q n a ha hproj).hasRegularCartierEquations_of_effective_weil _
    (candidateSupportCartier_effective q n a ha hproj)

/-- The actual divisor ideal, without square-root or supplied ideal data. -/
def candidateSupportIdeal : (sourceSurface q n a ha hproj).toScheme.IdealSheafData :=
  effectiveCartierIdealDataOfRegularEquations (sourceSurface q n a ha hproj).toScheme
    (candidateSupportCartier q n a ha hproj)
    (candidateSupportCartier_hasRegularEquations q n a ha hproj)

/-- Its actual geometric support is the support of the original rational candidate. -/
theorem candidateSupportIdeal_support :
    ((candidateSupportIdeal q n a ha hproj).support :
        Set (sourceSurface q n a ha hproj).toScheme) =
      divisorSupport (candidate q n a ha hproj) := by
  classical
  let X := sourceSurface q n a ha hproj
  letI := X.stalks_uniqueFactorizationMonoid_of_regular
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
  ext x
  obtain ⟨c, hxc⟩ := candidateSupportCartier_hasRegularEquations q n a ha hproj x
  change x ∈ (effectiveCartierIdealDataOfRegularEquations X.toScheme
      (candidateSupportCartier q n a ha hproj)
      (candidateSupportCartier_hasRegularEquations q n a ha hproj)).support ↔ _
  rw [PrimeCurve.mem_support_iff_not_isUnit_germ _ _ c x hxc,
    X.regularCartierEquation_germ_isUnit_iff _ c ⟨x, hxc⟩, mem_divisorSupport]
  constructor
  · intro h
    by_contra hn
    apply h
    intro C hxC
    rw [candidateSupportCartier_multiplicity]
    split_ifs with hC
    · exact (hn ⟨C, Finsupp.mem_support_iff.mp hC, hxC⟩).elim
    · rfl
  · rintro ⟨C, hC, hxC⟩ hz
    have hzero := hz C hxC
    rw [candidateSupportCartier_multiplicity,
      if_pos (Finsupp.mem_support_iff.mpr hC)] at hzero
    exact one_ne_zero hzero

/-- The original support ideal is radical, by its computed zero-or-one multiplicities. -/
theorem candidateSupportIdeal_radical :
    (candidateSupportIdeal q n a ha hproj).radical = candidateSupportIdeal q n a ha hproj := by
  let X := sourceSurface q n a ha hproj
  letI := X.stalks_uniqueFactorizationMonoid_of_regular
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.radical_ideal, candidateSupportIdeal,
    effectiveCartierIdealDataOfRegularEquations_ideal]
  apply (X.cartierSectionIdeal_isRadical _
    (candidateSupportCartier_effective q n a ha hproj) ?_ U.1).radical
  intro C
  rw [candidateSupportCartier_weil]
  exact X.selectedPrimeWeil_le_one _ C

/-- Equality of the actual Cartier ideal with the original reduced support ideal. -/
theorem candidateSupportIdeal_eq_vanishingIdeal :
    candidateSupportIdeal q n a ha hproj = Scheme.IdealSheafData.vanishingIdeal
      ⟨divisorSupport (candidate q n a ha hproj), divisorSupport_isClosed _⟩ := by
  calc
    candidateSupportIdeal q n a ha hproj = (candidateSupportIdeal q n a ha hproj).radical :=
      (candidateSupportIdeal_radical q n a ha hproj).symm
    _ = Scheme.IdealSheafData.vanishingIdeal (candidateSupportIdeal q n a ha hproj).support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = _ := congrArg Scheme.IdealSheafData.vanishingIdeal
      (SetLike.coe_injective (candidateSupportIdeal_support q n a ha hproj))

end KltDP.Examples.FrobeniusDiscrepancyBounds
