import KltDP.Geometry.SelectedPrimeCurveCartierUnion
import KltDP.Geometry.PrimeCurvePairingSupport

/-!
# A disjoint selected Cartier sum restricts by the selected curve's self-intersection

The original Cartier-to-Weil equality supplies the finite prime expansion.
Every other selected curve contributes zero by actual geometric
disjointness and the proved intersection-support criterion. Only the
original curve's diagonal contribution remains.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- The original selected Cartier sum meets a selected disjoint curve by its actual self-number. -/
theorem intersectionNumber_selected_disjoint_sum
    (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (C : S.PrimeCurve) (hC : C ∈ N) :
    C.intersectionNumber E = C.selfIntersectionNumber hregular := by
  classical
  rw [S.intersectionNumber_eq_weil_sum hregular C E, hE]
  unfold Finsupp.sum
  rw [S.selectedPrimeWeil_support, Finset.sum_eq_single C]
  · rw [S.selectedPrimeWeil_apply, if_pos hC]
    change 1 * C.selfIntersectionNumber hregular = C.selfIntersectionNumber hregular
    exact one_mul _
  · intro D hDN hDC
    rw [S.selectedPrimeWeil_apply, if_pos hDN]
    change 1 * C.intersectionNumber (S.primeCurveCartier hregular D) = 0
    rw [one_mul]
    rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
      S hregular C D]
    exact (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      S hregular C D hDC.symm).mpr (hdisj hC hDN hDC.symm)
  · intro hCN
    exact (hCN hC).elim

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.intersectionNumber_selected_disjoint_sum
