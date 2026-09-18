import KltDP.Geometry.IsolatedNodePicardIndexUnimodular
import KltDP.Geometry.IsolatedNodePicardPairing
import KltDP.Lattices.OrthogonalSpanEven

/-!
# The actual Picard index bound from unimodularity and the original splitting

The selected node classes retain the original smooth Weil-to-Picard map.
Their geometric pairings are even, and span induction extends that fact
to their integer span. The specified complementary submodule pairs to zero
with each node. Its sum with that span therefore supplies the pairing
hypothesis of the already proved original Picard index bound.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface UnbranchedExceptionalBlocks

/-- Original Picard unimodularity constructs the basis; the actual orthogonal
submodule decomposition supplies the required even pairings. -/
theorem isolated_nodes_card_le_picard_index_factorization_of_picardUnimodular_of_orthogonal_splitting
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X π)
    (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1)
    (p : ℕ) [CharP k p] (hp : 2 < p)
    (hU : S.PicardUnimodular hmin.regular)
    (N : Finset S.PrimeCurve) (hiso : IsolatedSelection π N)
    (hN : ∀ C ∈ N, IsExceptionalCurve π C)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hmin.regular = -2)
    (Γ : Submodule ℤ (Additive S.toScheme.Pic)) [Γ.toAddSubgroup.FiniteIndex]
    (Γ0 : Submodule ℤ (Additive S.toScheme.Pic))
    (hΓ : letI : IsSmooth S.structureMorphism :=
      MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
      Γ = Γ0 ⊔ Submodule.span ℤ (Set.range
        (fun C : {C : S.PrimeCurve // C ∈ N} =>
          S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C.val 1)))))
    (horth : letI : IsSmooth S.structureMorphism :=
      MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
      ∀ C : {C : S.PrimeCurve // C ∈ N}, ∀ y ∈ Γ0,
        S.integralPicardIntersectionBilinForm hmin.regular
          (S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C.val 1))) y = 0) :
    N.card ≤ Γ.toAddSubgroup.index.factorization 2 := by
  letI : IsSmooth S.structureMorphism :=
    MinimalResolutionQuadraticRegular.source_isSmooth π hmin
  let v : {C : S.PrimeCurve // C ∈ N} → Additive S.toScheme.Pic := fun C =>
    S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C.val 1))
  have hpair : ∀ C, ∀ y ∈ Γ,
      Even (S.integralPicardIntersectionBilinForm hmin.regular (v C) y) :=
    KltDP.Lattices.OrthogonalSpanEven.even_pairing
      (S.integralPicardIntersectionBilinForm hmin.regular) v Γ Γ0 hΓ horth
      (fun C D => S.isolatedSelection_nodePicard_pairing_even
        hmin.regular π N hiso hN hself C D)
  exact isolated_nodes_card_le_picard_index_factorization_of_picardUnimodular
    π hmin hDP hrank p hp hU N hiso hN hself Γ hpair

end KltDP.Geometry

#check @KltDP.Geometry.isolated_nodes_card_le_picard_index_factorization_of_picardUnimodular_of_orthogonal_splitting
#print axioms KltDP.Geometry.isolated_nodes_card_le_picard_index_factorization_of_picardUnimodular_of_orthogonal_splitting
