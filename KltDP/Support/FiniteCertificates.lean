import KltDP.Support.TenRowValues
import KltDP.Manuscript.S09.RootedTrees
import KltDP.Lattices.SmallADEForestDecomposition
import Mathlib.Tactic

/-!
# F32: finite certificates and completeness infrastructure (packaging)

Supporting obligation F32 (`planning/AUTOFORMALIZATION_PLAN.md` §6 "F32",
`planning/THEOREM_MAP.json` id F32; source passage `source/manuscript.tex`
lines 2491–2509, the proof of `lem:rooted-trees`, together with the ten-forest
lemma `lem:ten-forests`, lines 2514–2578). The plan's exports
`KltDP.Geometry.rationalMatrixCertificate_sound`,
`forestEnumerator_complete_upTo_labeledIso`, `integerContactEnumerator_complete`,
`finiteCaseCertificate_kernelChecked` are provided in `KltDP.Support`. This
module only packages accepted theorems; every proof term below is an
application of an accepted declaration, except the eight-element cardinality
`Fintype.card RootedBlockChoice = 8` (kernel `decide`).

* Certificate soundness: `rationalMatrixCertificate_sound` — each of the ten
  row models carries an exact rational matrix with `A * A⁻¹ = 1 = A⁻¹ * A`,
  inverse-source equations and all table scalars (accepted
  `KltDP.Support.tenRow_model_certificate`); `rootedMatrixCertificate_table`
  and `rootedMatrixCertificate_realized` — the eight rooted-tree matrices with
  their edge counts, root inverse entries and positive definiteness (accepted
  `KltDP.Manuscript.S09.rootedTrees_table`, `rootedTrees_table_realized`).
* Enumeration completeness up to label-preserving isomorphism:
  `forestEnumerator_complete_upTo_labeledIso` — under the original hypotheses of
  `lem:ten-forests` exactly one of the ten rows is realized, with a graph
  isomorphism from the row's marked weighted model fixing the three marks and
  all weights (accepted `tenCandidateForests_of_originalHypotheses`);
  `forestEnumerator_uniqueRow`, `forestEnumerator_labeledIso`,
  `forestEnumerator_rows_iff`; `rootedTreeEnumerator_complete_upTo_rootedIso`
  and `rootedTreeEnumerator_complete` — every rooted tree with at most three
  edges is root-preservingly isomorphic to one of the eight listed shapes, with
  its matrix, inverse root entry and canonical correction identified (accepted
  `smallRootedTree_classification`, `KltDP.Manuscript.S09.rootedTrees`);
  `smallForest_componentEnumerator_complete` (accepted
  `eight_vertex_forest_determinant_rows`).
* Integer contact/charge enumerations: `integerContactEnumerator_complete` —
  the finite charge sets `S₁`, `S₂`, the three-edge set and its interval
  filter, with the completeness equivalence `mem_rootedPairCharges_iff`;
  `integerContactEnumerator_complete_trees` for arbitrary trees;
  `integerCountEnumerator_complete` — the rank/partition rows (accepted
  `mem_rankEightRows_iff`, `mem_rankEightSquareRows_iff`, `mem_betaSquareRows_iff`).
* Numerical predicates versus manuscript hypotheses:
  `manuscriptHypotheses_imply_rows`, `manuscriptHypotheses_realized_of_determinant`
  (accepted `TenForestOriginalHypotheses.classification`,
  `.realized_of_determinant`): `TenForestOriginalHypotheses` is the literal
  conjunction of the manuscript hypotheses and is never a conclusion.
* Kernel checking: `finiteCaseCertificate_kernelChecked` bundles the
  finite-table facts (ten rows, injective exceptional determinants, table
  identities, square rows, edge counts and connectivity of the eight shapes).
  That *no* certificate anywhere in the import closure uses native evaluation
  is not a theorem inside Lean; it is enforced by two separate gates: the
  source policy `scripts/audit_sources.py` (lexical rejection of
  `native_decide`, `ofReduce*`, `skipKernelTC`, `addDeclWithoutChecking`,
  `extern`, `implemented_by`, `unsafe`, `axiom`, and of any `attribute` command
  outside the two reviewed forms; record `audit/source_lint.json`) and the
  compiled Trust audit `KltDP.Audit.Trust` (`#klt_trust_report`, driver
  `audit/CompiledTrust.lean`), which traverses every project declaration's
  kernel-checked type, value, inductive and recursor data and rejects any axiom
  outside `propext`, `Classical.choice`, `Quot.sound` and the admitted
  literature allowlist; see `docs/TRUST_AUDIT.md`. Every `decide` in the cited
  modules is plain kernel reduction.
* `f32_core` bundles the clauses.

Not present in the accepted code, and therefore not claimed here: a generic
checker (`rationalMatrixCertificate`-style data type plus a soundness theorem
`checker c = true → property`); the certificates are concrete Lean terms whose
properties are proved directly. No declaration named `SmallTableEightTotal*`
exists in the accepted tree; the corresponding content is
`SmallADEPartitions.rankEight_*` and `eight_vertex_forest_determinant_rows`.
-/

universe u

namespace KltDP.Support

open Matrix SimpleGraph KltDP.LinearAlgebra KltDP.Manuscript.S09
open KltDP.Lattices.SmallADEPartitions

/-! ### Certificate soundness -/

/-- **Rational matrix certificates.** Each row model has an exact rational
matrix whose determinant, two-sided inverse, inverse-source equations and all
table scalars are proved (accepted `tenRow_model_certificate`). -/
theorem rationalMatrixCertificate_sound (row : TenForestRow) : TenRowModelCertificate row :=
  tenRow_model_certificate row

/-- The eight rooted-tree rows: edge counts and root inverse entries as
functions of the root weight `b` (accepted `rootedTrees_table`). -/
theorem rootedMatrixCertificate_table (b : ℚ) :
    (rootedBlockEdges (.arms .point) = 0 ∧ rootedBlockGreen (.arms .point) b = 1 / b) ∧
    (rootedBlockEdges (.arms .endEdge) = 1 ∧
      rootedBlockGreen (.arms .endEdge) b = 2 / (2 * b - 1)) ∧
    (rootedBlockEdges (.arms .endTwo) = 2 ∧
      rootedBlockGreen (.arms .endTwo) b = 3 / (3 * b - 2)) ∧
    (rootedBlockEdges (.arms .middleTwo) = 2 ∧
      rootedBlockGreen (.arms .middleTwo) b = 1 / (b - 1)) ∧
    (rootedBlockEdges (.arms .endThree) = 3 ∧
      rootedBlockGreen (.arms .endThree) b = 4 / (4 * b - 3)) ∧
    (rootedBlockEdges (.arms .innerThree) = 3 ∧
      rootedBlockGreen (.arms .innerThree) b = 6 / (6 * b - 7)) ∧
    (rootedBlockEdges (.arms .centerStar) = 3 ∧
      rootedBlockGreen (.arms .centerStar) b = 2 / (2 * b - 3)) ∧
    (rootedBlockEdges .leafStar = 3 ∧ rootedBlockGreen .leafStar b = 1 / (b - 1)) :=
  rootedTrees_table b

/-- Each listed rooted shape is an actual positive-definite rooted tree with the
stated edge count, valency bound and root inverse entry (accepted
`rootedTrees_table_realized`). -/
theorem rootedMatrixCertificate_realized (choice : RootedBlockChoice) {b : ℚ} (hb : 3 ≤ b) :
    (rootedBlockGraph choice).IsTree ∧
    (rootedGraphMatrix (rootedBlockGraph choice) (rootedBlockRoot choice) b).PosDef ∧
    (rootedBlockGraph choice).edgeFinset.card = rootedBlockEdges choice ∧
    (∀ v, (rootedBlockGraph choice).degree v ≤ 3) ∧
    rootedTreeGreen (rootedBlockGraph choice) (rootedBlockRoot choice) b =
      rootedBlockGreen choice b :=
  rootedTrees_table_realized choice hb

/-! ### Enumeration completeness up to label-preserving isomorphism -/

/-- **Forest enumerator completeness.** Under the original hypotheses of
`lem:ten-forests` (the conjunction `TenForestOriginalHypotheses`), `β ≠ 5` and
exactly one of the ten rows is realized; the realization data include a graph
isomorphism from the row's marked weighted model to `G` fixing the three
distinguished vertices and every weight, the transported matrix, inverse,
sources, determinants and remaining-forest invariants (accepted
`tenCandidateForests_of_originalHypotheses`). -/
theorem forestEnumerator_complete_upTo_labeledIso {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {weight : V → ℕ} {coeff : V → ℚ}
    {C B D : V} {β : ℕ} (h : TenForestOriginalHypotheses G weight coeff C B D β) :
    β ≠ 5 ∧ ∃! row : TenForestRow, TenCandidateForestData row G weight coeff C B D β :=
  tenCandidateForests_of_originalHypotheses h

/-- The unique row label, with its graph witnesses (accepted
`TenForestRows.existsUnique_realized` composed with the classifier). -/
theorem forestEnumerator_uniqueRow {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {weight : V → ℕ} {coeff : V → ℚ}
    {C B D : V} {β : ℕ} (h : TenForestOriginalHypotheses G weight coeff C B D β) :
    ∃! row : TenForestRow, row.Realized G weight coeff C B D β :=
  TenForestRows.existsUnique_realized G weight coeff C B D β h.classification

/-- The label-preserving isomorphism for a realized row (accepted
`TenForestRow.Realized.weighted_graph_iso`). -/
theorem forestEnumerator_labeledIso {V : Type*} [Fintype V] [DecidableEq V]
    {row : TenForestRow} {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (h : row.Realized G weight coeff C B D β)
    (hcard : Fintype.card V = β + 7)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β) (hBD : B ≠ D) :
    ∃ f : row.modelGraph ≃g G,
      f row.modelC = C ∧ f row.modelB = B ∧ f row.modelD = D ∧
      ∀ v, weight (f v) = row.modelWeight v :=
  h.weighted_graph_iso hcard hC hB hD hBD

/-- The classifier's disjunction is exactly the union of the ten labelled
realizations (accepted `tenForestRows_iff_exists_realized`). -/
theorem forestEnumerator_rows_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ) :
    TenForestRows G weight coeff C B D β ↔
      ∃ row : TenForestRow, row.Realized G weight coeff C B D β :=
  tenForestRows_iff_exists_realized G weight coeff C B D β

/-- **Rooted-tree enumerator completeness.** Every finite rooted tree with at
most three edges is root-preservingly isomorphic to one of the eight listed
shapes (accepted `smallRootedTree_classification`). -/
theorem rootedTreeEnumerator_complete_upTo_rootedIso {V : Type*} [Fintype V]
    {G : SimpleGraph V} [Fintype G.edgeSet] (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3)
    (root : V) :
    ∃ choice : RootedBlockChoice, ∃ e : G ≃g rootedBlockGraph choice,
      e root = rootedBlockRoot choice :=
  smallRootedTree_classification hG hedges root

/-- The rooted-tree enumeration with its matrix data: valency bound, the
shape, its edge count, the matrix identification, the root inverse entry and
the canonical-degree corrections (accepted `KltDP.Manuscript.S09.rootedTrees`;
positive definiteness is a source premise). -/
theorem rootedTreeEnumerator_complete {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) {b : ℚ} (hb : 3 ≤ b)
    (hA : (rootedGraphMatrix G root b).PosDef) :
    (∀ v, G.degree v ≤ 3) ∧
      ∃ choice : RootedBlockChoice, ∃ e : G ≃g rootedBlockGraph choice,
        e root = rootedBlockRoot choice ∧
        rootedBlockEdges choice = G.edgeFinset.card ∧
        (rootedBlockMatrixAt choice b).submatrix e.toEquiv e.toEquiv =
          rootedGraphMatrix G root b ∧
        rootedTreeGreen G root b = rootedBlockGreen choice b ∧
        (fun v => rootedGraphMatrix G root b v v - 2) =
          Pi.single (f := fun _ : V => ℚ) root (b - 2) ∧
        ((rootedGraphMatrix G root b)⁻¹ *ᵥ
          Pi.single (f := fun _ : V => ℚ) root (b - 2)) root =
            (b - 2) * rootedBlockGreen choice b ∧
        dotProduct (Pi.single (f := fun _ : V => ℚ) root (b - 2))
          ((rootedGraphMatrix G root b)⁻¹ *ᵥ
            Pi.single (f := fun _ : V => ℚ) root (b - 2)) =
              (b - 2) ^ 2 * rootedBlockGreen choice b :=
  rootedTrees G root hG hedges hb hA

/-- Small-forest component enumeration: an acyclic graph on eight vertices with
at least five components realizes one of the eight rank-partition rows with its
Cartan matrix and determinant (accepted `eight_vertex_forest_determinant_rows`). -/
theorem smallForest_componentEnumerator_complete {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ c : G.ConnectedComponent, Fintype c.supp]
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent) :
    ∃ counts : Counts, ∃ e : V ≃ KltDP.Lattices.SmallADEMatrices.Vertex counts,
      (KltDP.Lattices.SmallADEMatrices.cartanMatrix counts).submatrix e e =
        KltDP.Lattices.SmallADEGraphs.graphCartanMatrix G ∧
      counts ∈ rankEightRows ∧
      (KltDP.Lattices.SmallADEGraphs.graphCartanMatrix G).det = (counts.rootDet : ℤ) :=
  KltDP.Lattices.SmallADEForestDecomposition.eight_vertex_forest_determinant_rows G hG hvertices
    hcomponents

/-! ### Integer contact and count enumerations -/

/-- **Integer contact enumerator completeness.** The finite charge sets of the
source proof (`S₁`, `S₂`, the three-edge set and its interval filter), with the
completeness equivalence: a rational is in `rootedPairCharges budget` iff it is
the sum of the actual root inverse entries of two listed shapes within the edge
budget (accepted `mem_rootedPairCharges_iff`, `rootedPairCharges_one/two/three`,
`rootedPairCharges_three_interval`). -/
theorem integerContactEnumerator_complete :
    (∀ (budget : ℕ) (charge : ℚ), charge ∈ rootedPairCharges budget ↔
      ∃ choiceA choiceB : RootedBlockChoice,
        rootedBlockEdges choiceA + rootedBlockEdges choiceB ≤ budget ∧
          rootedBlockActualCharge choiceA + rootedBlockActualCharge choiceB = charge) ∧
    rootedPairCharges 1 = {2 / 3, 11 / 15} ∧
    rootedPairCharges 2 = {2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5} ∧
    rootedPairCharges 3 =
      {2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5, 7 / 9, 29 / 33, 1, 29 / 35, 9 / 10} ∧
    (rootedPairCharges 3).filter (fun charge => 13 / 15 < charge ∧ charge ≤ 14 / 15) =
      {29 / 33, 9 / 10} :=
  ⟨fun budget charge => mem_rootedPairCharges_iff budget charge, rootedPairCharges_one,
    rootedPairCharges_two, rootedPairCharges_three, rootedPairCharges_three_interval⟩

/-- The same enumeration for two arbitrary actual trees with at most three
edges in total, with converse occurrence (accepted `rootedTrees_pairs_three`). -/
theorem integerContactEnumerator_complete_trees {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 3) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ∈
      ({2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5, 7 / 9, 29 / 33, 1, 29 / 35, 9 / 10} :
        Finset ℚ) ∧
    ∀ charge : ℚ, RootedPairRealization 3 charge ↔
      charge ∈ ({2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5, 7 / 9, 29 / 33, 1, 29 / 35, 9 / 10} :
        Finset ℚ) :=
  rootedTrees_pairs_three G H rootG rootH hG hH hbudget

/-- **Integer count enumerator completeness.** The rank-eight partition rows,
the square rows and the `β`-square rows are exactly the listed finite tables
(accepted `mem_rankEightRows_iff`, `mem_rankEightSquareRows_iff`,
`mem_betaSquareRows_iff`; the listed rows are verified by kernel `decide`). -/
theorem integerCountEnumerator_complete :
    (∀ c : Counts, c ∈ rankEightRows ↔ c.rank = 8 ∧ 5 ≤ c.components) ∧
    (∀ (c : Counts) (I : ℕ), (I, c) ∈ rankEightSquareRows ↔
      c.rank = 8 ∧ 5 ≤ c.components ∧ c.rootDet = I ^ 2) ∧
    (∀ (c : Counts) (beta I : ℕ), (beta, I, c) ∈ betaSquareRows ↔
      3 ≤ beta ∧ beta ≤ 5 ∧ c.rank = beta + 3 ∧ 5 ≤ c.components ∧
        (6 - beta) * c.rootDet = I ^ 2) :=
  ⟨mem_rankEightRows_iff, mem_rankEightSquareRows_iff, mem_betaSquareRows_iff⟩

/-! ### Numerical input predicates and the manuscript hypotheses -/

/-- The manuscript hypotheses of `lem:ten-forests`, as the literal conjunction
`TenForestOriginalHypotheses`, imply the classifier's row disjunction (accepted
`TenForestOriginalHypotheses.classification`). -/
theorem manuscriptHypotheses_imply_rows {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {weight : V → ℕ} {coeff : V → ℚ}
    {C B D : V} {β : ℕ} (h : TenForestOriginalHypotheses G weight coeff C B D β) :
    TenForestRows G weight coeff C B D β :=
  h.classification

/-- A proved exceptional determinant identifies the realized row (accepted
`TenForestOriginalHypotheses.realized_of_determinant`). -/
theorem manuscriptHypotheses_realized_of_determinant {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {weight : V → ℕ} {coeff : V → ℚ}
    {C B D : V} {β : ℕ} (h : TenForestOriginalHypotheses G weight coeff C B D β)
    (row : TenForestRow)
    (hd : (graphWeightMatrix G (fun i => (weight i : ℚ))).det = row.exceptionalDet) :
    row.Realized G weight coeff C B D β :=
  h.realized_of_determinant row hd

/-! ### Kernel-checked finite tables and nonvacuity -/

/-- **Kernel-checked finite case tables.** The finite data of the ten-row and
eight-shape tables: ten rows, injective exceptional determinants, the table
identities, the absolute bordered determinants, the three square rows, the
edge counts and connectivity of the eight rooted shapes, and eight shapes. All
are proved by kernel reduction (`decide`/`norm_num`) in the accepted modules;
the absence of native evaluation in the whole closure is enforced by the source
lint and the Trust audit (see the module docstring). -/
theorem finiteCaseCertificate_kernelChecked :
    Fintype.card TenForestRow = 10 ∧
    Function.Injective TenForestRow.exceptionalDet ∧
    (∀ row : TenForestRow,
      0 < row.volume ∧ row.volume ≤ row.length ∧
      row.volume * (row.green - 1) = row.length ^ 2 ∧
      row.borderedDet = (-1 : ℚ) ^ (row.beta + 7) * row.exceptionalDet * (row.green - 1) ∧
      |row.borderedDet| = row.deltaFactor * row.remainingDet) ∧
    (∀ row : TenForestRow, |row.borderedDet| = (tenRowAbsoluteDet row : ℚ)) ∧
    (∀ row : TenForestRow,
      IsSquare (tenRowAbsoluteDet row) ↔ row = .a2 ∨ row = .d1 ∨ row = .e2) ∧
    (∀ choice : RootedBlockChoice,
      (rootedBlockGraph choice).edgeFinset.card = rootedBlockEdges choice ∧
        (rootedBlockGraph choice).Connected) ∧
    Fintype.card RootedBlockChoice = 8 :=
  ⟨TenForestRow.card_rows, TenForestRow.exceptionalDet_injective, TenForestRow.table_identities,
    tenRow_absoluteDet_cast, tenRow_square_iff,
    fun choice => ⟨rootedBlockGraph_edge_count choice, rootedBlockGraph_connected choice⟩,
    by decide⟩

/-- **Nonvacuity of every finite case.** Each of the ten rows has an actual
finite marked weighted forest satisfying all original hypotheses and the
complete named conclusion, together with its model certificate (accepted
`u_ten_row_values_graph_nonvacuity`); each of the eight rooted shapes is an
actual positive-definite rooted tree (accepted `rootedTrees_table_realized`). -/
theorem finiteCaseCertificate_nonvacuous :
    (∀ row : TenForestRow, TenRowModelCertificate row ∧
      ∃ (G : SimpleGraph (Fin (row.beta + 7))) (adj : DecidableRel G.Adj)
        (weight : Fin (row.beta + 7) → ℕ) (coeff : Fin (row.beta + 7) → ℚ)
        (C B D : Fin (row.beta + 7)),
        letI : DecidableRel G.Adj := adj
        TenForestOriginalHypotheses G weight coeff C B D row.beta ∧
          TenCandidateForestData row G weight coeff C B D row.beta) ∧
    (∀ (choice : RootedBlockChoice) {b : ℚ}, 3 ≤ b →
      (rootedBlockGraph choice).IsTree ∧
      (rootedGraphMatrix (rootedBlockGraph choice) (rootedBlockRoot choice) b).PosDef ∧
      (rootedBlockGraph choice).edgeFinset.card = rootedBlockEdges choice ∧
      (∀ v, (rootedBlockGraph choice).degree v ≤ 3) ∧
      rootedTreeGreen (rootedBlockGraph choice) (rootedBlockRoot choice) b =
        rootedBlockGreen choice b) :=
  ⟨u_ten_row_values_graph_nonvacuity, fun choice _ hb => rootedTrees_table_realized choice hb⟩

/-! ### The bundle -/

/-- **F32 core.** Exact rational model certificates for the ten rows; forest
enumeration completeness up to marked weighted isomorphism under the original
hypotheses; rooted-tree enumeration completeness up to root-preserving
isomorphism; completeness of the integer contact (charge) enumeration; the
rank/partition table; the square rows; nonvacuity of all ten rows; and the
kernel-checked row count. -/
theorem f32_core :
    (∀ row : TenForestRow, TenRowModelCertificate row) ∧
    (∀ {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
      {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ},
      TenForestOriginalHypotheses G weight coeff C B D β →
        β ≠ 5 ∧ ∃! row : TenForestRow, TenCandidateForestData row G weight coeff C B D β) ∧
    (∀ {V : Type u} [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet], G.IsTree →
      G.edgeFinset.card ≤ 3 → ∀ root : V,
        ∃ choice : RootedBlockChoice, ∃ e : G ≃g rootedBlockGraph choice,
          e root = rootedBlockRoot choice) ∧
    (∀ (budget : ℕ) (charge : ℚ), charge ∈ rootedPairCharges budget ↔
      ∃ choiceA choiceB : RootedBlockChoice,
        rootedBlockEdges choiceA + rootedBlockEdges choiceB ≤ budget ∧
          rootedBlockActualCharge choiceA + rootedBlockActualCharge choiceB = charge) ∧
    (∀ c : Counts, c ∈ rankEightRows ↔ c.rank = 8 ∧ 5 ≤ c.components) ∧
    (∀ row : TenForestRow,
      IsSquare (tenRowAbsoluteDet row) ↔ row = .a2 ∨ row = .d1 ∨ row = .e2) ∧
    (∀ row : TenForestRow,
      ∃ (G : SimpleGraph (Fin (row.beta + 7))) (adj : DecidableRel G.Adj)
        (weight : Fin (row.beta + 7) → ℕ) (coeff : Fin (row.beta + 7) → ℚ)
        (C B D : Fin (row.beta + 7)),
        letI : DecidableRel G.Adj := adj
        TenForestOriginalHypotheses G weight coeff C B D row.beta ∧
          TenCandidateForestData row G weight coeff C B D row.beta) ∧
    Fintype.card TenForestRow = 10 :=
  ⟨rationalMatrixCertificate_sound,
    fun h => forestEnumerator_complete_upTo_labeledIso h,
    fun hG hedges root => rootedTreeEnumerator_complete_upTo_rootedIso hG hedges root,
    integerContactEnumerator_complete.1,
    integerCountEnumerator_complete.1,
    tenRow_square_iff,
    tenCandidateForests_all_rows_nonvacuous,
    TenForestRow.card_rows⟩

end KltDP.Support
