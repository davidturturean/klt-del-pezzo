import KltDP.Manuscript.S05.PicardIndex
import KltDP.Support.SmallTableEightTotalComponents

/-!
# Section 5.4 of the manuscript: an eight-curve weight-two forest has at most four components

Manuscript `source/manuscript.tex`, Lemma 5.4 (`lem:eight-curve-forest`, lines 1442–1481).
Let `F ⊂ D` be a union of connected components of the exceptional forest consisting of eight
weight-two curves (encoded: a finset `F` of vertices, closed under adjacency, with `F.card = 8`
and `R.w v = 2` on `F`). Suppose an integral nondegenerate unimodular sublattice `U ⊂ Pic S` is
orthogonal to `F` (encoded: a family `u : α → Pic S` with `|det Gram(u)| = 1`, orthogonal to the
classes of `F`) and `U ⊕ ⟨F⟩` has full rank (encoded: `card α + 8 = ρ(S) = card R.Vertices + 1`).
Then the induced forest on `F` has at most four connected components.

The lattice content is the union's `components_le_four_of_no_isolated_half_sum` (the eight-shape
determinant table, index-square equation and integral node code); this file supplies the
geometric inputs: the unimodular basis of `Pic S` of the right rank (`finrank_pic`), the Gram
matrix of the classes of `F` as the negative Cartan matrix of the induced forest
(`A_eq_graphWeightMatrix`), acyclicity of the exceptional graph, and the no-even-node theorem
(`isolated_nodes_no_half_sum`, Theorem 5.1) in characteristic `p > 2`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Codes KltDP.LinearAlgebra KltDP.Lattices.SmallADEForestLattice
open KltDP.Lattices.SmallADEGraphs
open scoped BigOperators

universe u

namespace KltDP.Manuscript.S05

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-- The exceptional dual graph of the klt minimal resolution is a forest. -/
theorem graph_isAcyclic : R.graph.IsAcyclic :=
  (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.2.1

/-- Every induced subgraph of the exceptional forest is a forest. -/
theorem induce_isAcyclic (s : Set R.Vertices) : (R.graph.induce s).IsAcyclic := by
  intro v c hc
  let f := SimpleGraph.Embedding.comap (Function.Embedding.subtype s) R.graph
  have hinj : Function.Injective ⇑f.toHom := fun a b h => f.injective h
  exact graph_isAcyclic R (c.map f.toHom)
    ((SimpleGraph.Walk.map_isCycle_iff_of_injective hinj).mpr hc)

/-- **Lemma 5.4 (`lem:eight-curve-forest`)**: in characteristic `p > 2`, an eight-curve
weight-two union `F` of connected components of the exceptional forest, orthogonal to a
unimodular sublattice `U = ⟨u⟩` with `U ⊕ ⟨F⟩` of full rank in `Pic S`, has at most four
connected components. -/
theorem eightWeightTwoCurves (p : ℕ) [CharP k p] (hp : 2 < p)
    (F : Finset R.Vertices) (hF : F.card = 8) (hw : ∀ v ∈ F, R.w v = 2)
    (hclosed : ∀ v ∈ F, ∀ y, R.graph.Adj v y → y ∈ F)
    {α : Type u} [Fintype α] [DecidableEq α] (u : α → Additive R.S.toScheme.Pic)
    (hu : (familyGram (R.S.integralPicardIntersectionBilinForm R.hreg) u).det.natAbs = 1)
    (hperp : ∀ v ∈ F, ∀ i, R.S.integralPicardIntersectionBilinForm R.hreg (cls R v) (u i) = 0)
    (hfull : Fintype.card α + 8 = Fintype.card R.Vertices + 1) :
    Nat.card (R.graph.induce (F : Set R.Vertices)).ConnectedComponent ≤ 4 := by
  classical
  let s : Set R.Vertices := (F : Set R.Vertices)
  let G : SimpleGraph s := R.graph.induce s
  letI : Fintype s := Fintype.ofFinite s
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  letI : ∀ c : G.ConnectedComponent, Fintype c.supp := fun c => Fintype.ofFinite _
  have hvert : Fintype.card s = 8 := by
    have h1 : Fintype.card s = Nat.card s := Fintype.card_eq_nat_card
    have h2 : Nat.card s = F.card := Nat.card_eq_finsetCard F
    omega
  have hU := picardUnimodular R p (by omega)
  obtain ⟨hfree, hfin⟩ := R.S.picard_free_and_finite_of_picardUnimodular R.hreg hU
  letI := hfree
  letI := hfin
  have hcard : Fintype.card (Fin (Module.finrank ℤ (Additive R.S.toScheme.Pic))) =
      Fintype.card (α ⊕ s) := by
    rw [Fintype.card_fin, Fintype.card_sum, finrank_pic R p (by omega), hvert]
    omega
  let b : Basis (α ⊕ s) ℤ (Additive R.S.toScheme.Pic) :=
    (Module.finBasis ℤ (Additive R.S.toScheme.Pic)).reindex (Fintype.equivOfCardEq hcard)
  have hb : (BilinForm.toMatrix b (R.S.integralPicardIntersectionBilinForm R.hreg)).det.natAbs
      = 1 :=
    KltDP.Lattices.PerfectIntegralGram.toMatrix_det_natAbs_eq_one b _
      (R.S.integralPicardIntersectionBilinForm_bijective_of_picardUnimodular R.hreg hU)
  let w : s → Additive R.S.toScheme.Pic := fun v => cls R v.val
  have hGram : familyGram (R.S.integralPicardIntersectionBilinForm R.hreg) w =
      -graphCartanMatrix G := by
    ext v x
    apply Int.cast_injective (α := ℚ)
    have h := pairing_cls R v.val x.val
    have hA := congr_fun (congr_fun R.A_eq_graphWeightMatrix v.val) x.val
    rw [graphWeightMatrix_apply] at hA
    have hM : R.M v.val x.val = -R.A v.val x.val := by simp [ResolutionDatum.A]
    change (R.S.integralPicardIntersectionBilinForm R.hreg (cls R v.val) (cls R x.val) : ℚ) =
      ((-graphCartanMatrix G v x : ℤ) : ℚ)
    rw [h, hM, hA]
    have hadj : G.Adj v x ↔ R.graph.Adj v.val x.val := Iff.rfl
    by_cases hvx : v = x
    · subst hvx
      simp [graphCartanMatrix, hw v.val v.property]
    · have hvx' : v.val ≠ x.val := fun h' => hvx (Subtype.ext h')
      by_cases had : R.graph.Adj v.val x.val
      · simp [graphCartanMatrix, hvx, hvx', had, hadj]
      · simp [graphCartanMatrix, hvx, hvx', had, hadj]
  have hnoEven : ∀ J : Finset s, J.Nonempty → (∀ v ∈ J, v ∉ G.support) →
      ¬ ∃ m : Additive R.S.toScheme.Pic, (2 : ℤ) • m = ∑ v ∈ J, w v := by
    rintro J hJ hJiso ⟨m, hm⟩
    refine isolated_nodes_no_half_sum R p hp (J.map ⟨Subtype.val, Subtype.val_injective⟩)
      (Finset.Nonempty.map hJ) ?_ ?_ ⟨m, ?_⟩
    · intro W hW
      obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hW
      exact hw v.val v.property
    · intro W hW y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hW
      have hyF : y ∈ F := hclosed _ v.property y hy
      exact hJiso v hv ((SimpleGraph.mem_support G).mpr ⟨⟨y, hyF⟩, hy⟩)
    · rw [hm, Finset.sum_map]
      rfl
  have h := components_le_four_of_no_isolated_half_sum G (induce_isAcyclic R s) hvert b _ hb u w
    hu (fun v i => hperp v.val v.property i) hGram hnoEven
  rw [Nat.card_eq_fintype_card]
  exact h

end KltDP.Manuscript.S05

#print axioms KltDP.Manuscript.S05.eightWeightTwoCurves
