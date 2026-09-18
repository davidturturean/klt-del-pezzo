import KltDP.Examples.FrobeniusMultiCentreCanonicalRetainedPairing
import KltDP.Examples.FrobeniusMultiCentreContractingClass

/-!
# The integral canonical relation on the original finite-centre surface

The original atlas canonical class and the original embedded graph and fibre
classes are identified with their integral vectors by previously proved
comparisons. Apply the existing realization homomorphism to an integer
coordinate identity. All subtractions in the coefficients are in integers.
No projectivity, positivity, canonical-descent or divisor-pushforward premise
is used. This is an identity in the original source Picard group.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalIntegralRelation

open KltDP.Geometry
open FrobeniusMultiCentreSurface FrobeniusMultiCentreCanonicalOpenComparison
open FrobeniusMultiCentreCanonicalRetainedPairing
open FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreFiberGlobalClass
open FrobeniusMultiCentrePicardRealization FrobeniusMultiCentreRealizedCurveClasses
open FrobeniusMultiCentreContractingClass

private theorem sum_fiberVector (p n : ℕ) :
    (∑ i : Fin n, FrobeniusPicard.fiberVector p n i) =
      (0, (n : ℤ), fun _ => (-1 : ℤ)) := by
  classical
  ext ij <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, FrobeniusPicard.fiberVector]

private theorem integral_vector_relation (p n : ℕ) :
    ((p : ℤ) * ((n : ℤ) - 2)) • FrobeniusPicard.canonicalVector p n +
      ((p : ℤ) * ((n : ℤ) - 2) - 2) • FrobeniusPicard.graphVector p n +
      (((n : ℤ) - 2) * ((p : ℤ) - 2)) •
        (∑ i : Fin n, FrobeniusPicard.fiberVector p n i) +
      (2 - ((p : ℤ) - 2) * ((n : ℤ) - 2)) • FrobeniusPicard.nefVector p n = 0 := by
  rw [sum_fiberVector]
  ext ij <;>
    simp [FrobeniusPicard.canonicalVector, FrobeniusPicard.graphVector,
      FrobeniusPicard.nefVector, smul_eq_mul] <;> ring

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- The denominator-cleared canonical relation uses the original atlas
canonical class, embedded strict-graph and strict-fibre kernel classes, and
original contracting class M. It is an equality of actual Picard classes. -/
theorem canonical_integral_relation :
    let p : ℤ := (q + 1 : ℕ)
    let r : ℤ := (n : ℤ) - 2
    let s : ℤ := p * r
    let d : ℤ := 2 - (p - 2) * r
    s • multiCanonicalClass (q + 1) n a ha +
      (s - 2) • (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) +
      (r * (p - 2)) •
        (∑ i : Fin n, -Additive.ofMul (fiberKernelLine q n a ha i).toPic) +
      d • contractingClass q n a ha = 0 := by
  dsimp only
  have h := congrArg (realization q n a) (integral_vector_relation (q + 1) n)
  simpa only [map_add, map_zsmul, map_sum, map_zero,
    ← multiCanonicalClass_eq_realization q n a ha,
    realization_graphVector q n a ha, realization_fiberVector q n a ha,
    ← contractingClass_eq_realization q n a ha] using h

end KltDP.Examples.FrobeniusMultiCentreCanonicalIntegralRelation
