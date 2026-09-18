import KltDP.Geometry.ExceptionalQCartierIntersection
import KltDP.Geometry.CompatibleCanonicalDifferenceSupport

/-!
# Original discrepancy rows in a finite exceptional family

Finite-support sums can be computed in any injective finite family containing
their actual support. For an original compatible canonical difference, an
enumeration of the original contracted primes provides this coverage. Its
matrix row is therefore the original source canonical degree, including
contracted primes whose discrepancy coefficient is zero.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Matrix
open scoped BigOperators
universe u v

namespace KltDP.Geometry.RationalWeilIntersection

open NormalProjectiveSurface BirationalWeilPushforward

/-- Reindex an actual rational Weil intersection by an injective finite family
containing the divisor's actual support. -/
theorem intersectionMatrix_mulVec_family
    {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
    {I : Type v} [Fintype I]
    (C : I → S.PrimeCurve) (hinj : Function.Injective C)
    (D : S.RationalWeilDivisor)
    (hcover : (D.support : Set S.PrimeCurve) ⊆ Set.range C) (i : I) :
    (NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ
      (fun j => D (C j))) i = degreeLinearMap S hregular (C i) D := by
  classical
  have hsupp : D.support ⊆ Finset.univ.image C := by
    intro E hE
    obtain ⟨j, hj⟩ := hcover hE
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
  have hsum : degreeLinearMap S hregular (C i) D =
      ∑ j : I, D (C j) *
        ((C i).intersectionNumber (S.primeCurveCartier hregular (C j)) : ℚ) := by
    rw [degreeLinearMap_apply]
    calc
      _ = ∑ E ∈ Finset.univ.image C,
          D E * ((C i).intersectionNumber (S.primeCurveCartier hregular E) : ℚ) := by
        apply Finset.sum_subset hsupp
        intro E hE hn
        rw [Finsupp.not_mem_support_iff.mp hn, zero_mul]
      _ = _ := Finset.sum_image (fun _ _ _ _ h => hinj h)
  rw [hsum]
  simp only [Matrix.mulVec, dotProduct, NullCurveIntersectionMatrix.intersectionMatrix]
  apply Finset.sum_congr rfl
  intro j hj
  rw [S.intersectionPairing_symm hregular
      (S.primeCurveCartier hregular (C i)) (S.primeCurveCartier hregular (C j)),
    S.intersectionPairing_primeCurve]
  exact mul_comm _ _

/-- Every row of the original exceptional matrix applied to the literal
compatible difference is the original source canonical degree. Support
coverage follows from exact pushforward and the given original enumeration. -/
theorem intersectionMatrix_mulVec_compatible_difference
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (KS : CartierDivisor S.toScheme) (KX : X.WeilDivisor)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hpush : pushforward π hbir (S.cartierToWeilHom KS) = KX)
    {I : Type v} [Fintype I]
    (C : I → S.PrimeCurve) (hinj : Function.Injective C)
    (hcontracted : ∀ i, IsExceptionalCurve π (C i))
    (hcover : ∀ E : S.PrimeCurve, IsExceptionalCurve π E → E ∈ Set.range C) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    ∀ i : I,
      (NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ
        (fun j => (S.rationalCartierToWeilHom KS -
          QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) (C j))) i =
        ((C i).intersectionNumber KS : ℚ) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  intro i
  have hsupp := MinimalResolutionDiscrepancy.difference_support_subset_exceptional
    π hbir KS KX hK hpush
  rw [intersectionMatrix_mulVec_family S hregular C hinj _
    (fun E hE => hcover E (hsupp hE)) i]
  exact degreeLinearMap_difference hregular π hπ KS
    (rationalizeWeilDivisor X KX) hK (C i) (hcontracted i)

end KltDP.Geometry.RationalWeilIntersection

#check @KltDP.Geometry.RationalWeilIntersection.intersectionMatrix_mulVec_compatible_difference
#print axioms KltDP.Geometry.RationalWeilIntersection.intersectionMatrix_mulVec_family
#print axioms KltDP.Geometry.RationalWeilIntersection.intersectionMatrix_mulVec_compatible_difference
