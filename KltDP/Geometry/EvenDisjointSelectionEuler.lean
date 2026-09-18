import KltDP.Geometry.InverseCartierEulerCorrection
import KltDP.Geometry.SelectedPrimeCartierIntersection

/-!
# The original even selection has cardinality divisible by four

For a finite disjoint selection of minus-two curves, the actual selected
Cartier divisor has square minus twice the cardinality. An equality in
the integral Picard group to twice an original Cartier class gives the
half-class square. Its canonical intersection is zero when the original
selected curves have canonical degree zero. The proved Euler form of RR
then computes the exact integral Euler difference and forces divisibility
by four. No double-cover cohomology comparison is needed for this step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
open scoped BigOperators

universe u

set_option autoImplicit false

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- The original selected Weil coefficients compute the pairing with any Cartier divisor. -/
theorem selectedPrime_intersectionPairing
    (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (D : CartierDivisor S.toScheme) :
    intersectionPairing S hregular E D = ∑ C ∈ N, C.intersectionNumber D := by
  classical
  rw [S.intersectionPairing_eq_weil_sum_right hregular, hE]
  unfold Finsupp.sum
  rw [S.selectedPrimeWeil_support]
  apply Finset.sum_congr rfl
  intro C hC
  rw [S.selectedPrimeWeil_apply, if_pos hC]
  exact one_mul _

/-- The actual selected disjoint minus-two divisor has square minus twice its count. -/
theorem selectedPrime_intersectionPairing_self
    (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hregular = -2) :
    intersectionPairing S hregular E E = -2 * (N.card : ℤ) := by
  classical
  rw [S.selectedPrime_intersectionPairing hregular N E hE E]
  calc
    ∑ C ∈ N, C.intersectionNumber E = ∑ _C ∈ N, (-2 : ℤ) := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [S.intersectionNumber_selected_disjoint_sum hregular N E hE hdisj C hC,
        hself C hC]
    _ = -2 * (N.card : ℤ) := by simp [mul_comm]

/-- RR computes an actual integer whose quadruple is the original count. -/
theorem even_disjoint_selection_euler_difference
    (N : Finset S.PrimeCurve) (E D K : CartierDivisor S.toScheme)
    (hE : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (heven : cartierPicardClass S.toScheme E = cartierPicardClass S.toScheme (D + D))
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hregular = -2)
    (hK : ∀ C ∈ N, C.intersectionNumber K = 0)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2) :
    (N.card : ℤ) = 4 *
      (eulerCharacteristic S.structureMorphism
          (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) -
        eulerCharacteristic S.structureMorphism (cartierDivisorModule S.toScheme (-D))) := by
  classical
  have hleft (A : CartierDivisor S.toScheme) :
      intersectionPairing S hregular E A = intersectionPairing S hregular (D + D) A :=
    S.intersectionPairing_eq_of_class_eq_left hregular
      (S.primeCurveIntersectionSymmetric hregular) E (D + D) A heven
  have hdiag := S.selectedPrime_intersectionPairing_self hregular N E hE hdisj hself
  rw [hleft E, S.intersectionPairing_eq_of_class_eq_right hregular (D + D) E
    (D + D) heven] at hdiag
  simp only [S.intersectionPairing_add_left, S.intersectionPairing_add_right] at hdiag
  have hcanonical : intersectionPairing S hregular E K = 0 := by
    rw [S.selectedPrime_intersectionPairing hregular N E hE K]
    exact Finset.sum_eq_zero fun C hC => hK C hC
  rw [hleft K, S.intersectionPairing_add_left] at hcanonical
  have hDK : intersectionPairing S hregular D K = 0 := by omega
  have hRR := S.inverseCartier_euler_riemannRoch_twice hregular K eK D
  rw [S.intersectionPairing_add_right, hDK, add_zero] at hRR
  omega

/-- Integrality of the original surface Euler characteristic gives the
four-divisibility before any comparison with the double cover. -/
theorem four_dvd_card_of_even_disjoint_selection
    (N : Finset S.PrimeCurve) (E D K : CartierDivisor S.toScheme)
    (hE : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (heven : cartierPicardClass S.toScheme E = cartierPicardClass S.toScheme (D + D))
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hregular = -2)
    (hK : ∀ C ∈ N, C.intersectionNumber K = 0)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2) :
    4 ∣ N.card := by
  apply Int.natCast_dvd_natCast.mp
  exact ⟨_, S.even_disjoint_selection_euler_difference hregular N E D K
    hE heven hdisj hself hK eK⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.four_dvd_card_of_even_disjoint_selection
#print axioms KltDP.Geometry.NormalProjectiveSurface.four_dvd_card_of_even_disjoint_selection
