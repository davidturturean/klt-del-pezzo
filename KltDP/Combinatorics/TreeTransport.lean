import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Group-valued transport on an actual tree

Labels live on actual oriented graph edges (`Dart`). Reversing an edge
inverts its label. Products along the unique root paths give a vertex
potential, normalized at the root, whose ratios recover every edge label.
Neither finiteness nor commutativity is required.

This is graph algebra. It does not construct a cover of curves or a
geometric gluing map from the graph labels.
-/

namespace KltDP.Combinatorics

open SimpleGraph

variable {V Γ : Type*} {G : SimpleGraph V}

section Monoid

variable [Monoid Γ]

/-- The ordered product of labels along the actual darts of a walk. -/
def walkTransport (label : G.Dart → Γ) {u v : V} (p : G.Walk u v) : Γ :=
  (p.darts.map label).prod

@[simp]
theorem walkTransport_nil (label : G.Dart → Γ) (u : V) :
    walkTransport label (SimpleGraph.Walk.nil : G.Walk u u) = 1 := by
  simp only [walkTransport, SimpleGraph.Walk.darts_nil, List.map_nil, List.prod_nil]

@[simp]
theorem walkTransport_cons (label : G.Dart → Γ) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkTransport label (.cons h p) = label ⟨(u, v), h⟩ * walkTransport label p := by
  simp only [walkTransport, SimpleGraph.Walk.darts_cons, List.map_cons, List.prod_cons]

/-- Transport respects ordered concatenation, also for noncommutative labels. -/
theorem walkTransport_append (label : G.Dart → Γ) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkTransport label (p.append q) = walkTransport label p * walkTransport label q := by
  simp only [walkTransport, SimpleGraph.Walk.darts_append, List.map_append, List.prod_append]

@[simp]
theorem walkTransport_concat (label : G.Dart → Γ) {u v w : V}
    (p : G.Walk u v) (h : G.Adj v w) :
    walkTransport label (p.concat h) = walkTransport label p * label ⟨(v, w), h⟩ := by
  rw [SimpleGraph.Walk.concat_eq_append, walkTransport_append,
    walkTransport_cons, walkTransport_nil, mul_one]

end Monoid

/-- Appending an edge to a path remains a path if its new endpoint is
absent. The proof uses the pinned reverse/cons path interface. -/
theorem path_concat_of_not_mem {r u v : V} {p : G.Walk r u}
    (hp : p.IsPath) (hv : v ∉ p.support) (huv : G.Adj u v) :
    (p.concat huv).IsPath := by
  apply (SimpleGraph.Walk.isPath_reverse_iff _).mp
  rw [SimpleGraph.Walk.reverse_concat]
  apply hp.reverse.cons
  simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hv

/-- In an actual acyclic graph, adjacent endpoints of two paths with the
same start differ by appending that edge in one of its two orientations. -/
theorem acyclic_paths_across_edge (hG : G.IsAcyclic) {r u v : V}
    (p : G.Walk r u) (q : G.Walk r v) (hp : p.IsPath) (hq : q.IsPath)
    (huv : G.Adj u v) :
    p = q.concat huv.symm ∨ q = p.concat huv := by
  classical
  by_cases hv : v ∈ p.support
  · have hprefix : p.takeUntil v hv = q :=
      congrArg Subtype.val (hG.path_unique ⟨_, hp.takeUntil hv⟩ ⟨q, hq⟩)
    have hsuffix : p.dropUntil v hv = huv.symm.toWalk :=
      congrArg Subtype.val (hG.path_unique ⟨_, hp.dropUntil hv⟩
        ⟨huv.symm.toWalk, SimpleGraph.Walk.IsPath.of_adj huv.symm⟩)
    left
    calc
      p = (p.takeUntil v hv).append (p.dropUntil v hv) := (p.take_spec hv).symm
      _ = q.concat huv.symm := by rw [hprefix, hsuffix]; rfl
  · right
    exact congrArg Subtype.val (hG.path_unique ⟨q, hq⟩
      ⟨p.concat huv, path_concat_of_not_mem hp hv huv⟩)

/-- A chosen actual root path, whose existence and uniqueness come from
the tree hypothesis. -/
noncomputable def treeRootPath (hG : G.IsTree) (root v : V) : G.Walk root v :=
  Classical.choose (hG.existsUnique_path root v).exists

theorem treeRootPath_isPath (hG : G.IsTree) (root v : V) :
    (treeRootPath hG root v).IsPath :=
  Classical.choose_spec (hG.existsUnique_path root v).exists

/-- The root path is the actual unique simple path, independently of the
choice used in its definition. -/
theorem treeRootPath_eq (hG : G.IsTree) (root v : V) (p : G.Walk root v)
    (hp : p.IsPath) : treeRootPath hG root v = p :=
  (hG.existsUnique_path root v).unique (treeRootPath_isPath hG root v) hp

@[simp]
theorem treeRootPath_self (hG : G.IsTree) (root : V) :
    treeRootPath hG root root = .nil :=
  treeRootPath_eq hG root root .nil SimpleGraph.Walk.IsPath.nil

/-- The actual ordered root-path product defining the normalized potential. -/
noncomputable def treePotential [Monoid Γ] (hG : G.IsTree)
    (label : G.Dart → Γ) (root v : V) : Γ :=
  walkTransport label (treeRootPath hG root v)

@[simp]
theorem treePotential_root [Monoid Γ] (hG : G.IsTree) (label : G.Dart → Γ)
    (root : V) : treePotential hG label root root = 1 := by
  rw [treePotential, treeRootPath_self, walkTransport_nil]

section Group

variable [Group Γ]

/-- Inverse reversal of actual edge labels reverses the full walk product. -/
theorem walkTransport_reverse (label : G.Dart → Γ)
    (hreverse : ∀ d : G.Dart, label d.symm = (label d)⁻¹)
    {u v : V} (p : G.Walk u v) :
    walkTransport label p.reverse = (walkTransport label p)⁻¹ := by
  induction p with
  | nil => simp only [SimpleGraph.Walk.reverse_nil, walkTransport_nil, inv_one]
  | @cons u v w huv p ih =>
      simp only [SimpleGraph.Walk.reverse_cons, walkTransport_append,
        walkTransport_cons, walkTransport_nil, mul_one, ih]
      have hr : label ⟨(v, u), huv.symm⟩ = (label ⟨(u, v), huv⟩)⁻¹ :=
        hreverse ⟨(u, v), huv⟩
      rw [hr, mul_inv_rev]

/-- The potential at the end of an actual edge is obtained by multiplying
the initial potential by that oriented edge's label. -/
theorem treePotential_edge (hG : G.IsTree) (label : G.Dart → Γ)
    (hreverse : ∀ d : G.Dart, label d.symm = (label d)⁻¹) (root : V)
    {u v : V} (huv : G.Adj u v) :
    treePotential hG label root v =
      treePotential hG label root u * label ⟨(u, v), huv⟩ := by
  change walkTransport label (treeRootPath hG root v) =
    walkTransport label (treeRootPath hG root u) * label ⟨(u, v), huv⟩
  obtain hp | hq := acyclic_paths_across_edge hG.IsAcyclic
    (treeRootPath hG root u) (treeRootPath hG root v)
    (treeRootPath_isPath hG root u) (treeRootPath_isPath hG root v) huv
  · have ht := congrArg (walkTransport label) hp
    have hr : label ⟨(v, u), huv.symm⟩ = (label ⟨(u, v), huv⟩)⁻¹ :=
      hreverse ⟨(u, v), huv⟩
    rw [walkTransport_concat, hr] at ht
    rw [ht]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  · rw [hq, walkTransport_concat]

/-- Every oriented edge label is the ratio of its endpoint potentials,
with the order fixed explicitly for a possibly noncommutative group. -/
theorem treePotential_ratio (hG : G.IsTree) (label : G.Dart → Γ)
    (hreverse : ∀ d : G.Dart, label d.symm = (label d)⁻¹) (root : V)
    (d : G.Dart) :
    label d = (treePotential hG label root d.fst)⁻¹ * treePotential hG label root d.snd := by
  apply eq_inv_mul_iff_mul_eq.mpr
  exact (treePotential_edge hG label hreverse root d.adj).symm

/-- Any potential with the stated edge ratios telescopes along every
actual walk. This statement does not require acyclicity. -/
theorem walkTransport_of_ratios (label : G.Dart → Γ) (potential : V → Γ)
    (hratio : ∀ d : G.Dart, label d = (potential d.fst)⁻¹ * potential d.snd)
    {u v : V} (p : G.Walk u v) :
    walkTransport label p = (potential u)⁻¹ * potential v := by
  induction p with
  | nil => simp only [walkTransport_nil, inv_mul_cancel]
  | @cons u v w huv p ih =>
      rw [walkTransport_cons, hratio ⟨(u, v), huv⟩, ih]
      simp only [mul_assoc, mul_inv_cancel_left]

/-- A root-normalized potential is determined uniquely by the actual
oriented edge labels. -/
theorem treePotential_unique (hG : G.IsTree) (label : G.Dart → Γ) (root : V)
    (potential : V → Γ) (hroot : potential root = 1)
    (hratio : ∀ d : G.Dart, label d = (potential d.fst)⁻¹ * potential d.snd) :
    potential = treePotential hG label root := by
  funext v
  have ht := walkTransport_of_ratios label potential hratio (treeRootPath hG root v)
  rw [hroot, inv_one, one_mul] at ht
  exact ht.symm

/-- Group-valued inverse-reversing edge labels on an actual tree have
one unique root-normalized vertex potential. -/
theorem existsUnique_treePotential (hG : G.IsTree) (label : G.Dart → Γ)
    (hreverse : ∀ d : G.Dart, label d.symm = (label d)⁻¹) (root : V) :
    ∃! potential : V → Γ, potential root = 1 ∧
      ∀ d : G.Dart, label d = (potential d.fst)⁻¹ * potential d.snd := by
  refine ⟨treePotential hG label root,
    ⟨treePotential_root hG label root, treePotential_ratio hG label hreverse root⟩, ?_⟩
  intro potential hp
  exact treePotential_unique hG label root potential hp.1 hp.2

end Group

end KltDP.Combinatorics
