import KltDP.Geometry.RationalTreePicardTreeConnectivity

/-!
# The remaining inheritance hypothesis: transverse germs on the complement of a leaf

BRIEF11, task 11b (started). With the tree half of `InheritsLeafHypotheses` proved
(`isTree_incidenceGraph_componentUnionScheme_compl`), the only remaining inheritance is that of
the transverse branch germs, `InheritsTransverseBranches`. It implies `InheritsLeafHypotheses`
(`inheritsLeafHypotheses_of_transverse`), and the kernel statement of `lem:tree-picard` is
exported with this single hypothesis (`rationalTreePicard_trivial_of_exponents_zero''`,
`multidegreeHom_injective_of_transverse`).

The proof of `InheritsTransverseBranches` itself (local rings of `Z_{Cᶜ}` and `X` agree at the
nodes off `C`; at the leaf node, when it lies on two other components, the cotangent dimension
descends through the closed immersion) is recorded as the remaining piece in
`LEMMA22_PROGRESS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

/-- Inheritance of the transverse branch germs from a curve to the complementary union of a leaf
component. -/
def InheritsTransverseBranches : Prop :=
  ∀ (Y : Scheme.{u}) [NoetherianSpace Y] [IsLocallyNoetherian Y] [AlgebraicGeometry.IsReduced Y]
    (C : ↥(irreducibleComponents Y)) (q : Y),
    C.1 ∩ (componentClosedUnion Y ({C}ᶜ) : Set Y) = {q} →
    topologicalKrullDim Y ≤ 1 → (componentPointIncidenceGraph Y).IsTree →
    HasTransverseComponentBranches Y →
    HasTransverseComponentBranches (componentUnionScheme Y ({C}ᶜ))

/-- The tree half of the inheritance is proved; only the transverse germs remain. -/
theorem inheritsLeafHypotheses_of_transverse (htrans : InheritsTransverseBranches.{u}) :
    InheritsLeafHypotheses.{u} := by
  intro Y _ _ _ C q hcut hdim hTree htransY
  exact ⟨isTree_incidenceGraph_componentUnionScheme_compl hTree hcut,
    htrans Y C q hcut hdim hTree htransY⟩

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The kernel statement of `lem:tree-picard`, with the identification data and the tree
inheritance discharged: only the inheritance of the transverse germs remains as a hypothesis. -/
theorem rationalTreePicard_trivial_of_exponents_zero'' (htrans : InheritsTransverseBranches.{u})
    (n : ℕ) :
    ∀ (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
      [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f],
      Nat.card ↥(irreducibleComponents X) = n →
      topologicalKrullDim X ≤ 1 → (componentPointIncidenceGraph X).IsTree →
      HasTransverseComponentBranches X → ExponentsZeroTrivial k X :=
  rationalTreePicard_trivial_of_exponents_zero' k (inheritsLeafHypotheses_of_transverse htrans) n

/-- The kernel half of `lem:tree-picard`, with only the transverse-germ inheritance as a
hypothesis. -/
theorem multidegreeHom_injective_of_transverse (htrans : InheritsTransverseBranches.{u})
    (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
    (htransX : HasTransverseComponentBranches X)
    (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1) :
    Function.Injective (multidegreeHom k X e) :=
  multidegreeHom_injective_of_inheritance' k (inheritsLeafHypotheses_of_transverse htrans) X f
    hdim hTree htransX e

end KltDP.Geometry.RationalTreePicard
