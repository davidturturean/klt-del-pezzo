import KltDP.LinearAlgebra.SeparatedBlockScalars

/-!
# Excluding the case with no additional higher-weight vertex

Only B and D contribute to the actual canonical source weight-2.
Positive marked length implies coeff(B)+coeff(D)<1. For beta at least
three, its source pairing is less than beta-2, so the original volume
2-beta+q dot coeff is negative.

This algebraic consequence does not need a row equation, graph shape,
invertibility, or a selected beta-three/four/five table. It applies to the
actual weight and coefficient functions over any linearly ordered field.
-/

namespace KltDP.LinearAlgebra

open Matrix

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- With no extra source, the actual canonical pairing and positive marked
length force negative volume for every beta at least three. -/
theorem no_extra_source_volume_neg
    (weight coeff : V → 𝕜) (C B D : V) (β : 𝕜)
    (hβ : 3 ≤ β) (hB : weight B = 3) (hD : weight D = β)
    (hBD : B ≠ D)
    (hother : ∀ v, v ≠ B → v ≠ D → weight v = 2)
    (hcoeff : ∀ v, 0 ≤ coeff v)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff) :
    2 - β + dotProduct (fun i => weight i - 2) coeff < 0 := by
  have hsource := canonical_source_sum_extras weight coeff B D (∅ : Finset V) β
    hBD hB hD (by simp)
    (fun i hiB hiD _ => hother i hiB hiD)
  simp only [Finset.sum_empty, add_zero] at hsource
  have hsum : coeff B + coeff D < 1 := by
    rw [threeMarkedSource_dotProduct] at hlength
    linarith only [hlength, hcoeff C]
  have hproduct : 0 < (β - 2) * (1 - (coeff B + coeff D)) :=
    mul_pos (by linarith only [hβ]) (by linarith only [hsum])
  have hslack : 0 ≤ (β - 3) * coeff B :=
    mul_nonneg (by linarith only [hβ]) (hcoeff B)
  rw [hsource]
  nlinarith only [hproduct, hslack]

/-- Source-facing impossibility of zero extras, including all three
source rows beta=3,4,5. Both positive quantities are the original actual
pairings rather than independently supplied scalar surrogates. -/
theorem no_extra_source_impossible
    (weight coeff : V → 𝕜) (C B D : V) (β : 𝕜)
    (hβ : 3 ≤ β) (hB : weight B = 3) (hD : weight D = β)
    (hBD : B ≠ D)
    (hother : ∀ v, v ≠ B → v ≠ D → weight v = 2)
    (hcoeff : ∀ v, 0 ≤ coeff v)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff)
    (hvolume : 0 < 2 - β + dotProduct (fun i => weight i - 2) coeff) : False := by
  have hnegative := no_extra_source_volume_neg weight coeff C B D β
    hβ hB hD hBD hother hcoeff hlength
  linarith only [hnegative, hvolume]

end KltDP.LinearAlgebra
