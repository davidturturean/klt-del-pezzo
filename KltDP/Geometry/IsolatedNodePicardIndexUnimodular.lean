import KltDP.Geometry.IsolatedNodeCodeVanishing
import KltDP.Geometry.UnimodularPicardFiniteBasis
import KltDP.Lattices.IntegralNodeObstruction

/-! The actual finite-index Picard obstruction on an original klt del Pezzo
resolution, using the supplied unimodularity of its original Picard pairing.
The basis is constructed from that proof, and the zero node code follows
from the same original geometry. All node and submodule objects are retained. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface UnbranchedExceptionalBlocks

/-- The number of original isolated nodes is bounded by the exponent of
two in the index of any actual sublattice pairing evenly with those nodes. -/
theorem isolated_nodes_card_le_picard_index_factorization_of_picardUnimodular
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
    (hpair : letI : IsSmooth S.structureMorphism :=
      MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
      ∀ C : {C : S.PrimeCurve // C ∈ N}, ∀ y ∈ Γ,
        Even (S.integralPicardIntersectionBilinForm hmin.regular
          (S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C.val 1))) y)) :
    N.card ≤ Γ.toAddSubgroup.index.factorization 2 := by
  classical
  letI : IsSmooth S.structureMorphism :=
    MinimalResolutionQuadraticRegular.source_isSmooth π hmin
  obtain ⟨n, b, hB⟩ := S.exists_picard_basis_det_natAbs_one_of_picardUnimodular hmin.regular hU
  have hlower :=
    KltDP.Lattices.IntegralNodeObstruction.integralNodeCode_finrank_ge_card_sub_index_factorization
      b (S.integralPicardIntersectionBilinForm hmin.regular) hB Γ
      (fun C : {C : S.PrimeCurve // C ∈ N} =>
        S.smoothWeilClassPicardEquiv (S.weilClassMap (Finsupp.single C.val 1))) hpair
  change Fintype.card {C : S.PrimeCurve // C ∈ N} -
    Γ.toAddSubgroup.index.factorization 2 ≤
      Module.finrank (ZMod 2) (selectedNodePicardCode π hmin N) at hlower
  rw [selectedNodePicardCode_eq_bot π hmin hDP hrank p hp N hiso hN hself] at hlower
  simp only [Fintype.card_coe, finrank_bot] at hlower
  omega

end KltDP.Geometry

#check @KltDP.Geometry.isolated_nodes_card_le_picard_index_factorization_of_picardUnimodular
#print axioms KltDP.Geometry.isolated_nodes_card_le_picard_index_factorization_of_picardUnimodular
