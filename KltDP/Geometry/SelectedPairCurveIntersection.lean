import KltDP.Geometry.SelectedPrimeCartierIntersection

/-!
# A selected pair contributes only its intersecting member

The original Cartier-to-Weil equality supplies the two prime terms.
Actual geometric disjointness with the second term makes that term's
intersection zero by the existing prime-curve support theorem. This
retains the other term's full intersection, including the diagonal case.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

local instance selectedPairCurveIntersectionDecidableEq : DecidableEq S.PrimeCurve :=
  Classical.decEq _

/-- Only the first selected prime contributes when the second is geometrically disjoint. -/
theorem intersectionNumber_selected_pair_of_disjoint
    (P Q R : S.PrimeCurve) (hQR : Q ≠ R)
    (hPR : Disjoint (P : Set S.toScheme) (R : Set S.toScheme))
    (E : CartierDivisor S.toScheme)
    (hE : S.cartierToWeilHom E = S.selectedPrimeWeil {Q, R}) :
    P.intersectionNumber E = P.intersectionNumber (S.primeCurveCartier hregular Q) := by
  classical
  have hne : P ≠ R := by
    intro h
    rw [← h] at hPR
    obtain ⟨x, hx⟩ := P.nonempty
    exact Set.disjoint_left.mp hPR hx hx
  have hz : P.intersectionNumber (S.primeCurveCartier hregular R) = 0 := by
    rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
      S hregular P R]
    exact (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      S hregular P R hne).mpr hPR
  rw [S.intersectionNumber_eq_weil_sum hregular P E, hE]
  unfold Finsupp.sum
  rw [S.selectedPrimeWeil_support, Finset.sum_pair hQR,
    S.selectedPrimeWeil_apply, if_pos (Finset.mem_insert_self Q {R}),
    S.selectedPrimeWeil_apply,
    if_pos (Finset.mem_insert_of_mem (Finset.mem_singleton_self R))]
  change 1 * P.intersectionNumber (S.primeCurveCartier hregular Q) +
    1 * P.intersectionNumber (S.primeCurveCartier hregular R) = _
  rw [hz, mul_zero, add_zero, one_mul]

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.intersectionNumber_selected_pair_of_disjoint
