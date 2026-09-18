import KltDP.Geometry.EvenDisjointSelectionEuler
import KltDP.Geometry.CompatibleRationalAdjunctionDegree
import KltDP.Geometry.SmoothSurfaceDivisorPicard

/-!
# Four-divisibility from the original smooth surface and even curve selection

The original integral Picard half-class is represented by an actual
Cartier divisor. The original selected Weil sum and constructed canonical
line supply the other Cartier divisors. Rational adjunction derives all
canonical degrees, so no degree, square, Euler or cohomology identity is
an input to the final divisibility result. Characteristic two is not
excluded: this argument uses only the original surface's RR formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

set_option autoImplicit false

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 S.structureMorphism]

local instance evenSelectionFourDivisibilitySmooth : IsSmooth S.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism

/-- An actual even finite disjoint selection of rational minus-two curves
has cardinality divisible by four. -/
theorem four_dvd_card_of_original_even_selection
    (N : Finset S.PrimeCurve)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hP1 : ∀ C ∈ N, ∃ η : C.toScheme ≅ projectiveSpace k 1,
      η.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber S.regularPoints_of_isSmooth = -2)
    (m : Additive S.toScheme.Pic)
    (heven : S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) =
      (2 : ℕ) • m) :
    4 ∣ N.card := by
  let E := S.smoothWeilCartierEquiv (S.selectedPrimeWeil N)
  let D := S.picardRepresentative m.toMul
  let K := SmoothCanonicalCartierRepresentative.cartierRepresentative S.structureMorphism
  have hE : S.cartierToWeilHom E = S.selectedPrimeWeil N :=
    S.cartierToWeil_smoothWeilCartierEquiv (S.selectedPrimeWeil N)
  have hD : cartierPicardClass S.toScheme D = m.toMul :=
    S.cartierPicardClass_picardRepresentative m.toMul
  have hclass : cartierPicardClass S.toScheme E = m.toMul ^ 2 := by
    change cartierPicardClass S.toScheme
      (S.smoothWeilCartierEquiv (S.selectedPrimeWeil N)) = _
    rw [← S.smoothWeilClassPicardEquiv_representative, heven, _root_.toMul_nsmul]
  have hevenD : cartierPicardClass S.toScheme E =
      cartierPicardClass S.toScheme (D + D) := by
    rw [cartierPicardClass_add, hD, ← pow_two]
    exact hclass
  let eK : cartierDivisorModule S.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2 :=
    SmoothCanonicalCartierExterior.representativeIsoExterior S.structureMorphism
  have hK : ∀ C ∈ N, C.intersectionNumber K = 0 := by
    intro C hC
    obtain ⟨η, hη⟩ := hP1 C hC
    have h := CompatibleRationalAdjunctionDegree.canonical_intersection_eq S
      S.regularPoints_of_isSmooth K eK C η hη
    rw [hself C hC] at h
    omega
  exact S.four_dvd_card_of_even_disjoint_selection S.regularPoints_of_isSmooth
    N E D K hE hevenD hdisj hself hK eK

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.four_dvd_card_of_original_even_selection
#print axioms KltDP.Geometry.NormalProjectiveSurface.four_dvd_card_of_original_even_selection
