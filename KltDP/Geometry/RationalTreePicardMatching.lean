import KltDP.Combinatorics.TreeTransport
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Branch-matching modules over a tree

The component rings and the two residue evaluations at each edge are actual
commutative algebras and algebra homomorphisms. Their equalizer is a subring of
the product of the component rings. A unit on each oriented edge twists the
residue matching equation and defines a module over that original subring.

If the graph is a tree and opposite labels are inverse, the existing graph
transport theorem gives an explicit linear equivalence from the twisted module
to the equalizer ring. Thus the matching module is free of rank one. Neither
the equalizer description of a nodal curve's structure sheaf nor descent of
line bundles through its normalization is assumed or claimed here. Those
geometric comparisons are still required for the rational-tree Picard lemma.
-/

noncomputable section

namespace KltDP.Geometry.RationalTreePicard

open SimpleGraph

variable {k V : Type*} [CommRing k] (G : SimpleGraph V)
  (R : V → Type*) [∀ v, CommRing (R v)] [∀ v, Algebra k (R v)]
  (ev : ∀ d : G.Dart, R d.fst →ₐ[k] k)

/-- The ring of component functions with equal values on the two branches
of each original edge. The two evaluations may differ at different nodes on
the same component. -/
def matchingRing : Subring (∀ v, R v) :=
  (AlgHom.equalizer
    (Pi.algHom k (fun _ : G.Dart => k)
      (fun d => (ev d).comp (Pi.evalAlgHom k R d.fst)))
    (Pi.algHom k (fun _ : G.Dart => k)
      (fun d => (ev d.symm).comp (Pi.evalAlgHom k R d.snd)))).toSubring

/-- Membership retains the original pair of branch evaluations. -/
theorem matchingRing_condition (r : matchingRing G R ev) (d : G.Dart) :
    ev d (r.val d.fst) = ev d.symm (r.val d.snd) :=
  congrFun r.property d

variable (g : G.Dart → kˣ)

/-- The actual component families satisfying the twisted branch equation. -/
def matchingSections : AddSubgroup (∀ v, R v) where
  carrier := {s | ∀ d : G.Dart,
    ev d (s d.fst) = (g d : k) * ev d.symm (s d.snd)}
  zero_mem' := by intro d; simp only [Pi.zero_apply, map_zero, mul_zero]
  add_mem' := by
    intro s t hs ht d
    change ev d (s d.fst + t d.fst) = (g d : k) * ev d.symm (s d.snd + t d.snd)
    rw [map_add, map_add, mul_add, hs d, ht d]
  neg_mem' := by
    intro s hs d
    change ev d (-s d.fst) = (g d : k) * ev d.symm (-s d.snd)
    rw [map_neg, map_neg, hs d, mul_neg]

/-- The equalizer ring acts by the original componentwise multiplication. -/
def matchingSMul (r : matchingRing G R ev) (s : matchingSections G R ev g) :
    matchingSections G R ev g :=
  ⟨fun v => r.val v * s.val v, by
    intro d
    change ev d (r.val d.fst * s.val d.fst) =
      (g d : k) * ev d.symm (r.val d.snd * s.val d.snd)
    rw [map_mul, map_mul, matchingRing_condition G R ev r d, s.property d, mul_left_comm]⟩

instance matchingSectionsModule :
    Module (matchingRing G R ev) (matchingSections G R ev g) where
  smul := matchingSMul G R ev g
  one_smul s := by
    apply Subtype.ext
    funext v
    change 1 * s.val v = s.val v
    exact one_mul _
  mul_smul r t s := by
    apply Subtype.ext
    funext v
    change (r.val v * t.val v) * s.val v = r.val v * (t.val v * s.val v)
    exact mul_assoc _ _ _
  smul_zero r := by
    apply Subtype.ext
    funext v
    change r.val v * 0 = 0
    exact mul_zero _
  smul_add r s t := by
    apply Subtype.ext
    funext v
    change r.val v * (s.val v + t.val v) = r.val v * s.val v + r.val v * t.val v
    exact mul_add _ _ _
  add_smul r t s := by
    apply Subtype.ext
    funext v
    change (r.val v + t.val v) * s.val v = r.val v * s.val v + t.val v * s.val v
    exact add_mul _ _ _
  zero_smul s := by
    apply Subtype.ext
    funext v
    change 0 * s.val v = 0
    exact zero_mul _

variable (b : V → kˣ) (hb : ∀ d : G.Dart, b d.fst * g d = b d.snd)

/-- Evaluation of an actual constant function at an original branch. -/
@[simp]
theorem eval_constant (d : G.Dart) (a : k) :
    ev d (algebraMap k (R d.fst) a) = a := by
  exact (ev d).commutes a

include hb in
/-- Rescaling by the vertex units removes the original node labels. -/
theorem scale_mem_matchingRing (s : matchingSections G R ev g) :
    (fun v => algebraMap k (R v) (b v : k) * s.val v) ∈ matchingRing G R ev := by
  funext d
  change ev d (algebraMap k (R d.fst) (b d.fst : k) * s.val d.fst) =
    ev d.symm (algebraMap k (R d.snd) (b d.snd : k) * s.val d.snd)
  have hreverse (a : k) : ev d.symm (algebraMap k (R d.snd) a) = a := by
    exact (ev d.symm).commutes a
  rw [map_mul, map_mul, eval_constant G R ev d (b d.fst : k),
    hreverse (b d.snd : k), s.property d, ← mul_assoc]
  exact congrArg (fun u : kˣ => (u : k) * ev d.symm (s.val d.snd)) (hb d)

include hb in
/-- The inverse vertex units give the reverse matching equation. -/
theorem inverse_vertex_equation (d : G.Dart) :
    (b d.fst)⁻¹ = g d * (b d.snd)⁻¹ := by
  rw [← hb d, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]

include hb in
/-- Inverse rescaling turns every untwisted component function into a
section satisfying the specified node equations. -/
theorem inverse_scale_mem (r : matchingRing G R ev) :
    (fun v => algebraMap k (R v) ((b v)⁻¹ : kˣ) * r.val v) ∈
      matchingSections G R ev g := by
  intro d
  change ev d (algebraMap k (R d.fst) ((b d.fst)⁻¹ : kˣ) * r.val d.fst) =
    (g d : k) * ev d.symm (algebraMap k (R d.snd) ((b d.snd)⁻¹ : kˣ) * r.val d.snd)
  have hreverse (a : k) : ev d.symm (algebraMap k (R d.snd) a) = a := by
    exact (ev d.symm).commutes a
  rw [map_mul, map_mul, eval_constant G R ev d ((b d.fst)⁻¹ : kˣ),
    hreverse ((b d.snd)⁻¹ : kˣ),
    matchingRing_condition G R ev r d, ← mul_assoc]
  exact congrArg (fun u : kˣ => (u : k) * ev d.symm (r.val d.snd))
    (inverse_vertex_equation G g b hb d)

/-- The explicit linear trivialization over the original equalizer ring. -/
def matchingLinearEquiv :
    matchingSections G R ev g ≃ₗ[matchingRing G R ev] matchingRing G R ev where
  toFun s := ⟨fun v => algebraMap k (R v) (b v : k) * s.val v,
    scale_mem_matchingRing G R ev g b hb s⟩
  invFun r := ⟨fun v => algebraMap k (R v) ((b v)⁻¹ : kˣ) * r.val v,
    inverse_scale_mem G R ev g b hb r⟩
  left_inv s := by
    apply Subtype.ext
    funext v
    change algebraMap k (R v) ((b v)⁻¹ : kˣ) *
      (algebraMap k (R v) (b v : k) * s.val v) = s.val v
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  right_inv r := by
    apply Subtype.ext
    funext v
    change algebraMap k (R v) (b v : k) *
      (algebraMap k (R v) ((b v)⁻¹ : kˣ) * r.val v) = r.val v
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  map_add' s t := by
    apply Subtype.ext
    funext v
    change algebraMap k (R v) (b v : k) * (s.val v + t.val v) =
      algebraMap k (R v) (b v : k) * s.val v + algebraMap k (R v) (b v : k) * t.val v
    exact mul_add _ _ _
  map_smul' r s := by
    apply Subtype.ext
    funext v
    change algebraMap k (R v) (b v : k) * (r.val v * s.val v) =
      r.val v * (algebraMap k (R v) (b v : k) * s.val v)
    exact mul_left_comm _ _ _

/-- On a tree, inverse-reversing node labels always admit the constructed
linear trivialization. No freeness or Picard conclusion is an input. -/
def treeMatchingLinearEquiv (hG : G.IsTree)
    (hreverse : ∀ d : G.Dart, g d.symm = (g d)⁻¹) (root : V) :
    matchingSections G R ev g ≃ₗ[matchingRing G R ev] matchingRing G R ev :=
  matchingLinearEquiv G R ev g (KltDP.Combinatorics.treePotential hG g root)
    (fun d => (KltDP.Combinatorics.treePotential_edge hG g hreverse root d.adj).symm)

end KltDP.Geometry.RationalTreePicard
