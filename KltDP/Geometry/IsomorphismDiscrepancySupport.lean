import KltDP.Geometry.IsomorphismDiscrepancy

/-!
# Discrepancy support under the original source isomorphism

The actual image prime preserves both the discrepancy coefficient and
the Cartier boundary coefficient. Thus literal finite-support containment
is preserved, without an independent support-transport premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsomorphismDiscrepancy

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T X : NormalProjectiveSurface k}

/-- The original pulled Cartier boundary contains the support of the
original composed discrepancy, even for arbitrary signed coefficients. -/
theorem support_subset_pullback (e : S.toScheme ≅ T.toScheme)
    (g : T.toScheme ⟶ X.toScheme) [GenericPointPreserving g]
    (K : CartierDivisor T.toScheme) (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (A : CartierDivisor T.toScheme)
    (hsupport : (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB).support ⊆
      (T.cartierToWeilHom A).support) :
    letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
    (S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom e.hom K) -
        QCartierPullback.pullback (e.hom ≫ g) B hB).support ⊆
      (S.cartierToWeilHom (DominantCartierPullback.pullbackHom e.hom A)).support := by
  letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
  intro C hC
  obtain ⟨D, hD, _, hDelta⟩ := exists_prime_preserving_discrepancy e g K B hB C
  obtain ⟨D', hD', _, hA, _⟩ := exists_prime_preserving_coefficients e C
  have hDD' : D = D' :=
    NormalProjectiveSurface.PrimeCurve.genericPoint_injective (hD.symm.trans hD')
  rw [hDD'] at hDelta
  apply Finsupp.mem_support_iff.mpr
  rw [hA A]
  apply Finsupp.mem_support_iff.mp
  apply hsupport
  apply Finsupp.mem_support_iff.mpr
  intro hz
  exact (Finsupp.mem_support_iff.mp hC) (hDelta.trans hz)

/-- The original pulled Cartier boundary and composed discrepancy retain
the three coefficient/support properties used in a finite point step. -/
theorem pullback_boundary_data (e : S.toScheme ≅ T.toScheme)
    (g : T.toScheme ⟶ X.toScheme) [GenericPointPreserving g]
    (K : CartierDivisor T.toScheme) (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (A : CartierDivisor T.toScheme)
    (hcoeff : ∀ D : T.PrimeCurve,
      T.cartierToWeilHom A D = 0 ∨ T.cartierToWeilHom A D = 1)
    (hsupport : (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB).support ⊆
      (T.cartierToWeilHom A).support)
    (hbound : ∀ D : T.PrimeCurve,
      (-1 : ℚ) < (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB) D) :
    letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
    let K' := DominantCartierPullback.pullbackHom e.hom K
    let A' := DominantCartierPullback.pullbackHom e.hom A
    let Delta := S.rationalCartierToWeilHom K' -
      QCartierPullback.pullback (e.hom ≫ g) B hB
    (∀ C : S.PrimeCurve,
      S.cartierToWeilHom A' C = 0 ∨ S.cartierToWeilHom A' C = 1) ∧
      Delta.support ⊆ (S.cartierToWeilHom A').support ∧
      ∀ C : S.PrimeCurve, (-1 : ℚ) < Delta C := by
  letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
  exact ⟨cartier_coefficients_zero_or_one e A hcoeff,
    support_subset_pullback e g K B hB A hsupport,
    discrepancy_gt_neg_one e g K B hB hbound⟩

end KltDP.Geometry.IsomorphismDiscrepancy
