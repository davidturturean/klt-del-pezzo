import KltDP.Combinatorics.TreeTransport
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Compatible roots of branch coefficients on an actual tree

An oriented edge records an actual invertible transition factor. If the
branch coefficients transform by the corresponding power, one root at a
chosen vertex extends uniquely to roots respecting every transition.
Over an algebraically closed field the initial nonzero root exists.

The general statement lifts vertex transport through a monoid morphism;
the square-root statement specializes it to the power map on field units.
These are algebraic compatibility results. They do not identify a dual
graph, construct a normalization atlas, or descend a line bundle or cover.
-/

noncomputable section

namespace KltDP.Combinatorics

open SimpleGraph

variable {V Γ Δ : Type*} {G : SimpleGraph V}

section Monoid

variable [Monoid Γ] [Monoid Δ]

/-- A monoid morphism commutes with the actual ordered edge product. -/
theorem walkTransport_map (f : Γ →* Δ) (label : G.Dart → Γ)
    {u v : V} (p : G.Walk u v) :
    f (walkTransport label p) = walkTransport (f ∘ label) p := by
  simp only [walkTransport, map_list_prod, List.map_map]

/-- An edge compatibility equation propagates along every actual walk;
no tree hypothesis is needed for this direction. -/
theorem vertex_eq_mul_walkTransport (label : G.Dart → Γ) (value : V → Γ)
    (hedge : ∀ d : G.Dart, value d.snd = value d.fst * label d)
    {u v : V} (p : G.Walk u v) :
    value v = value u * walkTransport label p := by
  induction p with
  | nil => simp only [walkTransport_nil, mul_one]
  | @cons u v w huv p ih =>
      rw [ih, hedge ⟨(u, v), huv⟩, walkTransport_cons, mul_assoc]

end Monoid

section Lift

variable [Group Γ] [Monoid Δ]

/-- Propagation from a specified value at the root, using the actual
unique paths of the tree. -/
def treeTransportLift (hG : G.IsTree) (label : G.Dart → Γ)
    (root : V) (start : Γ) (v : V) : Γ :=
  start * treePotential hG label root v

@[simp]
theorem treeTransportLift_root (hG : G.IsTree) (label : G.Dart → Γ)
    (root : V) (start : Γ) : treeTransportLift hG label root start root = start := by
  simp only [treeTransportLift, treePotential_root, mul_one]

/-- The lifted values respect every actual oriented edge. -/
theorem treeTransportLift_edge (hG : G.IsTree) (label : G.Dart → Γ)
    (hreverse : ∀ d : G.Dart, label d.symm = (label d)⁻¹)
    (root : V) (start : Γ) (d : G.Dart) :
    treeTransportLift hG label root start d.snd =
      treeTransportLift hG label root start d.fst * label d := by
  unfold treeTransportLift
  rw [treePotential_edge hG label hreverse root d.adj, mul_assoc]

/-- Compatibility of the target values is sufficient to lift all of
them, once the root value has been lifted. -/
theorem treeTransportLift_map (hG : G.IsTree) (label : G.Dart → Γ)
    (f : Γ →* Δ) (value : V → Δ)
    (hedge : ∀ d : G.Dart, value d.snd = value d.fst * f (label d))
    (root : V) (start : Γ) (hstart : f start = value root) (v : V) :
    f (treeTransportLift hG label root start v) = value v := by
  have h := vertex_eq_mul_walkTransport (f ∘ label) value hedge
    (treeRootPath hG root v)
  rw [← walkTransport_map] at h
  simpa only [treeTransportLift, map_mul, hstart, treePotential] using h.symm

/-- The lift is unique because actual walk transport determines every
vertex from its specified root value. -/
theorem treeTransportLift_unique (hG : G.IsTree) (label : G.Dart → Γ)
    (root : V) (start : Γ) (lifted : V → Γ) (hroot : lifted root = start)
    (hedge : ∀ d : G.Dart, lifted d.snd = lifted d.fst * label d) :
    lifted = treeTransportLift hG label root start := by
  funext v
  have h := vertex_eq_mul_walkTransport label lifted hedge (treeRootPath hG root v)
  rw [hroot] at h
  exact h

/-- A compatible vertex system lifts uniquely through a monoid morphism
after fixing one lift at an actual root of the tree. -/
theorem existsUnique_treeTransportLift (hG : G.IsTree) (label : G.Dart → Γ)
    (hreverse : ∀ d : G.Dart, label d.symm = (label d)⁻¹)
    (f : Γ →* Δ) (value : V → Δ)
    (hedge : ∀ d : G.Dart, value d.snd = value d.fst * f (label d))
    (root : V) (start : Γ) (hstart : f start = value root) :
    ∃! lifted : V → Γ, lifted root = start ∧
      (∀ v, f (lifted v) = value v) ∧
      ∀ d : G.Dart, lifted d.snd = lifted d.fst * label d := by
  refine ⟨treeTransportLift hG label root start, ?_, ?_⟩
  · exact ⟨treeTransportLift_root hG label root start,
      treeTransportLift_map hG label f value hedge root start hstart,
      treeTransportLift_edge hG label hreverse root start⟩
  · intro lifted hlifted
    exact treeTransportLift_unique hG label root start lifted hlifted.1 hlifted.2.2

end Lift

/-- Compatible power roots on a tree follow from one specified root.
The power map is Mathlib's existing monoid morphism. -/
theorem existsUnique_tree_power_roots [CommGroup Γ] (hG : G.IsTree)
    (label : G.Dart → Γ) (hreverse : ∀ d : G.Dart, label d.symm = (label d)⁻¹)
    (coefficient : V → Γ) (n : ℕ)
    (hedge : ∀ d : G.Dart, coefficient d.snd = coefficient d.fst * label d ^ n)
    (root : V) (start : Γ) (hstart : start ^ n = coefficient root) :
    ∃! lifted : V → Γ, lifted root = start ∧
      (∀ v, lifted v ^ n = coefficient v) ∧
      ∀ d : G.Dart, lifted d.snd = lifted d.fst * label d :=
  existsUnique_treeTransportLift hG label hreverse (powMonoidHom n)
    coefficient hedge root start hstart

section Field

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- A nonzero coefficient has a nonzero power root over the actual
algebraically closed field; the result is retained in its unit group. -/
theorem exists_unit_power_root (a : kˣ) {n : ℕ} (hn : 0 < n) :
    ∃ b : kˣ, b ^ n = a := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) hn
  have hb0 : b ≠ 0 := by
    intro hzero
    have ha0 : (a : k) = 0 := by
      rw [hzero, zero_pow (Nat.ne_of_gt hn)] at hb
      exact hb.symm
    exact a.ne_zero ha0
  refine ⟨Units.mk0 b hb0, ?_⟩
  apply Units.ext
  exact hb

/-- Actual invertible transition factors with compatible branch
coefficients have simultaneous roots. The only choice is at the root;
after that choice all vertex roots are forced. -/
theorem exists_tree_power_roots_of_isAlgClosed (hG : G.IsTree)
    (label : G.Dart → kˣ) (hreverse : ∀ d : G.Dart, label d.symm = (label d)⁻¹)
    (coefficient : V → kˣ) (n : ℕ) (hn : 0 < n)
    (hedge : ∀ d : G.Dart, coefficient d.snd = coefficient d.fst * label d ^ n)
    (root : V) :
    ∃ lifted : V → kˣ, (∀ v, lifted v ^ n = coefficient v) ∧
      ∀ d : G.Dart, lifted d.snd = lifted d.fst * label d := by
  obtain ⟨start, hstart⟩ := exists_unit_power_root (coefficient root) hn
  obtain ⟨lifted, hlifted, _⟩ :=
    existsUnique_tree_power_roots hG label hreverse coefficient n hedge root start hstart
  exact ⟨lifted, hlifted.2⟩

/-- The square-root case used for component branch coefficients. No
characteristic restriction is needed for this root-compatibility step;
splitting the quadratic cover still requires two to be invertible. -/
theorem exists_tree_square_roots_of_isAlgClosed (hG : G.IsTree)
    (label : G.Dart → kˣ) (hreverse : ∀ d : G.Dart, label d.symm = (label d)⁻¹)
    (coefficient : V → kˣ)
    (hedge : ∀ d : G.Dart, coefficient d.snd = coefficient d.fst * label d ^ 2)
    (root : V) :
    ∃ lifted : V → kˣ, (∀ v, lifted v ^ 2 = coefficient v) ∧
      ∀ d : G.Dart, lifted d.snd = lifted d.fst * label d :=
  exists_tree_power_roots_of_isAlgClosed hG label hreverse coefficient 2 zero_lt_two hedge root

end Field

end KltDP.Combinatorics
