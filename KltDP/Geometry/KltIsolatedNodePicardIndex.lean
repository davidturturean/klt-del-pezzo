import KltDP.Geometry.KltResolutionPicardCohomologyInvariants
import KltDP.Geometry.IsolatedNodeOrthogonalPicardIndexUnimodular

/-! The actual isolated-node index obstruction for the original rank-one
klt del Pezzo minimal resolution. Actual Picard unimodularity is derived
from the original geometry. The remaining submodule data are exactly the
original finite-index orthogonal splitting. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface UnbranchedExceptionalBlocks

theorem isolated_nodes_card_le_picard_index_of_kltDelPezzo
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X π)
    (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1)
    (p : ℕ) [CharP k p] (hp : 2 < p)
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
  have hU := (hmin.picard_and_structure_invariants_of_kltDelPezzo
    hDP hrank p (by omega)).1
  exact isolated_nodes_card_le_picard_index_factorization_of_picardUnimodular_of_orthogonal_splitting
    π hmin hDP hrank p hp hU N hiso hN hself Γ Γ0 hΓ horth

end KltDP.Geometry

#print axioms KltDP.Geometry.isolated_nodes_card_le_picard_index_of_kltDelPezzo
