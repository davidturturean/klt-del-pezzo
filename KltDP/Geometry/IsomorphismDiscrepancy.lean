import KltDP.Geometry.QCartierBirationalStalkCoefficient
import KltDP.Geometry.QCartierPullbackFunctorial

/-!
# Actual discrepancy coefficients under a source scheme isomorphism

The original isomorphism determines the original target prime and preserves
Cartier and Q-Cartier coefficients there. Applied to a Cartier numerator
minus the original composite pullback, this preserves the literal
discrepancy coefficients and their strict lower bound. No canonical
interpretation or independent coefficient equality is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsomorphismDiscrepancy

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T X : NormalProjectiveSurface k}

/-- The actual image prime preserves both integral Cartier coefficients
and all rational Cartier coefficients under the original isomorphism. -/
theorem exists_prime_preserving_coefficients (e : S.toScheme ≅ T.toScheme)
    (C : S.PrimeCurve) :
    letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
    ∃ D : T.PrimeCurve,
      e.hom.base C.genericPoint = D.genericPoint ∧
      e.hom.base '' (C : Set S.toScheme) = (D : Set T.toScheme) ∧
      (∀ K : CartierDivisor T.toScheme,
        S.cartierToWeilHom (DominantCartierPullback.pullbackHom e.hom K) C =
          T.cartierToWeilHom K D) ∧
      ∀ (B : T.RationalWeilDivisor) (hB : T.QCartier B),
        QCartierPullback.pullback e.hom B hB C = B D := by
  letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
  letI : IsProper e.hom := inferInstance
  have hbir : IsBirationalScheme e.hom :=
    ⟨genericPoint_eq_of_isOpenImmersion e.hom, inferInstance⟩
  letI : IsIso (e.hom.stalkMap C.genericPoint) := inferInstance
  obtain ⟨D, hD, hQ⟩ :=
    QCartierPullback.exists_prime_preserving_coefficients_of_stalkMap_isIso e.hom hbir C
  have hC : C = BirationalPrimeCorrespondence.abovePrimeCurve e.hom hbir D :=
    BirationalPrimeCorrespondence.abovePrimeCurve_unique e.hom hbir D C hD
  refine ⟨D, hD, ?_, ?_, hQ⟩
  · rw [hC]
    exact BirationalPrimeCorrespondence.abovePrimeCurve_image e.hom hbir D
  · intro K
    rw [hC]
    exact BirationalWeilPushforward.cartier_pullback_coefficient e.hom hbir K D

/-- Pulling the original Cartier numerator through the actual source
isomorphism preserves the original discrepancy at the actual image prime. -/
theorem exists_prime_preserving_discrepancy (e : S.toScheme ≅ T.toScheme)
    (g : T.toScheme ⟶ X.toScheme) [GenericPointPreserving g]
    (K : CartierDivisor T.toScheme) (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (C : S.PrimeCurve) :
    letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
    ∃ D : T.PrimeCurve,
      e.hom.base C.genericPoint = D.genericPoint ∧
      e.hom.base '' (C : Set S.toScheme) = (D : Set T.toScheme) ∧
      (S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom e.hom K) -
          QCartierPullback.pullback (e.hom ≫ g) B hB) C =
        (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB) D := by
  letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
  obtain ⟨D, hD, hImage, hK, hQ⟩ := exists_prime_preserving_coefficients e C
  have hNumerator :
      S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom e.hom K) C =
        T.rationalCartierToWeilHom K D := by
    change (S.cartierToWeilHom (DominantCartierPullback.pullbackHom e.hom K) C : ℚ) =
      (T.cartierToWeilHom K D : ℚ)
    exact congrArg (fun z : ℤ => (z : ℚ)) (hK K)
  have hPullback : QCartierPullback.pullback (e.hom ≫ g) B hB C =
      QCartierPullback.pullback g B hB D := by
    rw [QCartierPullback.pullback_comp]
    exact hQ _ (QCartierPullback.pullback_qCartier g B hB)
  refine ⟨D, hD, hImage, ?_⟩
  simp only [Finsupp.sub_apply, hNumerator, hPullback]

/-- Every strict discrepancy bound is preserved under the actual source
isomorphism, with the original composed morphism and Cartier pullback. -/
theorem discrepancy_gt_neg_one (e : S.toScheme ≅ T.toScheme)
    (g : T.toScheme ⟶ X.toScheme) [GenericPointPreserving g]
    (K : CartierDivisor T.toScheme) (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (h : ∀ D : T.PrimeCurve,
      (-1 : ℚ) < (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB) D) :
    letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
    ∀ C : S.PrimeCurve,
      (-1 : ℚ) <
        (S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom e.hom K) -
          QCartierPullback.pullback (e.hom ≫ g) B hB) C := by
  letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
  intro C
  obtain ⟨D, _, _, hD⟩ := exists_prime_preserving_discrepancy e g K B hB C
  rw [hD]
  exact h D

/-- A Cartier boundary with original integral coefficients zero or one
retains that condition after pullback by the actual scheme isomorphism. -/
theorem cartier_coefficients_zero_or_one (e : S.toScheme ≅ T.toScheme)
    (E : CartierDivisor T.toScheme)
    (hE : ∀ D : T.PrimeCurve,
      T.cartierToWeilHom E D = 0 ∨ T.cartierToWeilHom E D = 1) :
    letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
    ∀ C : S.PrimeCurve,
      S.cartierToWeilHom (DominantCartierPullback.pullbackHom e.hom E) C = 0 ∨
        S.cartierToWeilHom (DominantCartierPullback.pullbackHom e.hom E) C = 1 := by
  letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
  intro C
  obtain ⟨D, _, _, hK, _⟩ := exists_prime_preserving_coefficients e C
  simpa only [hK E] using hE D

end KltDP.Geometry.IsomorphismDiscrepancy
