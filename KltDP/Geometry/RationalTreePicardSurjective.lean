import KltDP.Geometry.RationalTreePicardExponentTransfer

/-!
# The surjectivity half of `lem:tree-picard`, modulo the node gluing of two line bundles

BRIEF14, step 4 (with step 3 as the hypothesis `NodeGluing`). By the same leaf induction as the
kernel half: on a single component every integer is realized
(`exists_componentExponent_eq_of_subsingleton`); at a leaf `C` with node `q`, the induction
hypothesis on `Z_{Cᶜ}` (components identified by `componentUnionIdentification`, exponents
transported by `componentExponent_componentUnionRestriction`) gives a line bundle with the prescribed
exponents off `C`, the projective line gives one with the prescribed exponent on `Z_C`
(`exists_chartExponent_eq`), and the node gluing `NodeGluing` produces a line bundle on `X` restricting
to both; its exponents are read on the two closed pieces (`chartExponent_congr_iso`,
`componentExponent_congr_iso`).

Exports: `exists_componentExponent_eq_of_nodeGluing`, `multidegreeHom_surjective_of_nodeGluing`,
`multidegreeHom_bijective_of_nodeGluing`, `multidegreeMulEquiv_of_nodeGluing`, and the bundle
`rationalTreePicard_of_nodeGluing` (the manuscript's `lem:tree-picard`, with the exact hypotheses
carried here and the node gluing as the single remaining hypothesis).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

/-- The node gluing of two line bundles (the remaining construction of BRIEF14, step 3): line
bundles on the leaf component and on the complementary union glue to a line bundle on the curve
restricting to both. -/
def NodeGluing : Prop :=
  ∀ (Y : Scheme.{u}) [NoetherianSpace Y] [IsLocallyNoetherian Y] [AlgebraicGeometry.IsReduced Y]
    (C : ↥(irreducibleComponents Y)) (q : Y),
    C.1 ∩ (componentClosedUnion Y ({C}ᶜ) : Set Y) = {q} →
    topologicalKrullDim Y ≤ 1 → (componentPointIncidenceGraph Y).IsTree →
    HasTransverseComponentBranches Y →
    ∀ (LC : InvertibleSheaf (componentUnionScheme Y {C}))
      (L' : InvertibleSheaf (componentUnionScheme Y ({C}ᶜ))),
      ∃ L : InvertibleSheaf Y,
        Nonempty ((schemeModulePullback (componentUnionInclusion Y {C})).obj L.obj ≅ LC.obj) ∧
        Nonempty ((schemeModulePullback (componentUnionInclusion Y ({C}ᶜ))).obj L.obj ≅ L'.obj)

variable (k : Type u) [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Every family of component exponents is realized by a line bundle, by the leaf induction, given
the node gluing. -/
theorem exists_componentExponent_eq_of_nodeGluing (hglue : NodeGluing.{u}) (n : ℕ) :
    ∀ (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
      [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f],
      Nat.card ↥(irreducibleComponents X) = n →
      topologicalKrullDim X ≤ 1 → (componentPointIncidenceGraph X).IsTree →
      HasTransverseComponentBranches X →
      ∀ (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
        (d : ↥(irreducibleComponents X) → ℤ),
        ∃ L : InvertibleSheaf X, ∀ C : ↥(irreducibleComponents X),
          componentExponent k X {C} (e C) L = d C := by
  refine Nat.strong_induction_on n ?_
  intro n IHn X _ _ _ f _ hcard hdim hTree htrans e d
  haveI hfin : Finite ↥(irreducibleComponents X) := by
    rw [Set.finite_coe_iff]
    exact NoetherianSpace.finite_irreducibleComponents
  have hne : Nonempty ↥(irreducibleComponents X) := nonempty_components_of_isTree X hTree
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hpos : 0 < Nat.card ↥(irreducibleComponents X) := Nat.card_pos
    have h1 : Nat.card ↥(irreducibleComponents X) = 1 := by omega
    haveI hsub : Subsingleton ↥(irreducibleComponents X) := (Nat.card_eq_one_iff_unique.mp h1).1
    obtain ⟨C⟩ := hne
    obtain ⟨L, hL⟩ := exists_componentExponent_eq_of_subsingleton k C (e C) (d C)
    refine ⟨L, fun C' => ?_⟩
    rw [Subsingleton.elim C' C]
    exact hL
  · haveI : Nontrivial ↥(irreducibleComponents X) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨C, q, hcut, -⟩ := exists_leafNodeChart X hdim hTree htrans
    obtain ⟨hTreeZ, htransZ⟩ := inheritsLeafHypotheses X C q hcut hdim hTree htrans
    obtain ⟨L', hL'⟩ := IHn _ (hcard ▸ card_components_componentUnionScheme_compl_lt X C)
      (componentUnionScheme X ({C}ᶜ)) (componentUnionInclusion X ({C}ᶜ) ≫ f) rfl
      (componentUnionScheme_topologicalKrullDim_le_one X _ hdim) hTreeZ htransZ
      ((componentUnionIdentification X ({C}ᶜ)).projectiveLineIso e)
      (fun D' => d (componentImage X ({C}ᶜ) D'))
    obtain ⟨LC, hLC⟩ := exists_chartExponent_eq k (e C) (d C)
    obtain ⟨L, ⟨iC⟩, ⟨iC'⟩⟩ := hglue X C q hcut hdim hTree htrans LC L'
    refine ⟨L, fun D => ?_⟩
    by_cases hDC : D = C
    · subst hDC
      exact (chartExponent_congr_iso k (e D) _ LC iC).trans hLC
    · obtain ⟨D', hD'⟩ := exists_componentImage_eq X ({C}ᶜ) D
        (fun h => hDC (Set.mem_singleton_iff.mp h))
      subst hD'
      rw [← componentExponent_componentUnionRestriction k ({C}ᶜ)
        (componentUnionIdentification X ({C}ᶜ)) e L D',
        componentExponent_congr_iso k {D'} _ (componentUnionRestriction X ({C}ᶜ) L) L' iC']
      exact hL' D'

variable (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
  [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
  (htrans : HasTransverseComponentBranches X)
  (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)

omit [IsAlgClosed k] in
include f hdim hTree htrans in
/-- The multidegree homomorphism is surjective, given the node gluing. -/
theorem multidegreeHom_surjective_of_nodeGluing (hglue : NodeGluing.{u}) :
    Function.Surjective (multidegreeHom k X e) :=
  (multidegreeHom_surjective_iff k X e).mpr fun d =>
    exists_componentExponent_eq_of_nodeGluing k hglue _ X f rfl hdim hTree htrans e d

include f hdim hTree htrans in
/-- The multidegree homomorphism is bijective, given the node gluing. -/
theorem multidegreeHom_bijective_of_nodeGluing (hglue : NodeGluing.{u}) :
    Function.Bijective (multidegreeHom k X e) :=
  ⟨multidegreeHom_injective_final k X f hdim hTree htrans e,
    multidegreeHom_surjective_of_nodeGluing k X f hdim hTree htrans e hglue⟩

/-- The Picard group of the rational tree as the free abelian group on its components, given the
node gluing. -/
def multidegreeMulEquiv_of_nodeGluing (hglue : NodeGluing.{u}) :
    X.Pic ≃* (↥(irreducibleComponents X) → Multiplicative ℤ) :=
  MulEquiv.ofBijective (multidegreeHom k X e)
    (multidegreeHom_bijective_of_nodeGluing k X f hdim hTree htrans e hglue)

include f hdim hTree htrans in
/-- `lem:tree-picard` (Picard group of a rational tree), with the exact hypotheses carried here:
`X` is a reduced Noetherian scheme, locally of finite type over an algebraically closed field `k`,
of dimension at most one, with tree component-point incidence graph (connectedness and acyclicity of
the incidence graph of components and their intersection points: "connected, dual graph a tree") and
transverse branch germs at the intersection points ("nodal"), and with each irreducible component
identified with the projective line. Then the multidegree map `Pic X → ℤ^{components}` (component
exponents through the identifications) is an isomorphism; the kernel half is unconditional
(`multidegreeHom_injective_final`), the surjectivity half is proved from the node gluing of two line
bundles (`NodeGluing`). -/
theorem rationalTreePicard_of_nodeGluing (hglue : NodeGluing.{u}) :
    Function.Bijective (multidegreeHom k X e) :=
  multidegreeHom_bijective_of_nodeGluing k X f hdim hTree htrans e hglue

end KltDP.Geometry.RationalTreePicard
