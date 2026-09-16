import KltDP.Geometry.RationalTreePicardMatching

/-!
# Removing node equations from branch-matching data

An open subset of a curve can omit nodes. At the algebraic matching level,
this removes edges and their residue equations. The original graph potential
still trivializes the remaining matching module, even when the remaining
graph is disconnected. These maps can be followed by the component algebra
restrictions in `RationalTreePicardRestriction`.
-/

noncomputable section

namespace KltDP.Geometry.RationalTreePicard

open SimpleGraph

variable {k V : Type*} [CommRing k] (G H : SimpleGraph V) (h : H ≤ G)
  (R : V → Type*) [∀ v, CommRing (R v)] [∀ v, Algebra k (R v)]
  (ev : ∀ d : G.Dart, R d.fst →ₐ[k] k) (g : G.Dart → kˣ)

/-- The original evaluations at the nodes that remain. Mathlib's graph
inclusion is the identity on vertices. -/
def retainedEvaluations (d : H.Dart) : R d.fst →ₐ[k] k :=
  ev ((SimpleGraph.Hom.ofLE h).mapDart d)

/-- The original unit labels at the nodes that remain. -/
def retainedLabels (d : H.Dart) : kˣ :=
  g ((SimpleGraph.Hom.ofLE h).mapDart d)

/-- Omitting node equations gives the identity-on-components map of rings. -/
def matchingRingForget :
    matchingRing G R ev →+* matchingRing H R (retainedEvaluations G H h R ev) where
  toFun r := ⟨r.val, by
    funext d
    exact matchingRing_condition G R ev r ((SimpleGraph.Hom.ofLE h).mapDart d)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The original twisted section remains a section after some of its
matching equations have been omitted. -/
def matchingSectionsForget :
    matchingSections G R ev g →ₛₗ[matchingRingForget G H h R ev]
      matchingSections H R (retainedEvaluations G H h R ev) (retainedLabels G H h g) where
  toFun s := ⟨s.val, fun d => s.property ((SimpleGraph.Hom.ofLE h).mapDart d)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A vertex gauge for all original nodes is also a gauge for the remaining
nodes. The remaining graph need not be connected. -/
theorem retained_vertex_equation (b : V → kˣ)
    (hb : ∀ d : G.Dart, b d.fst * g d = b d.snd) (d : H.Dart) :
    b d.fst * retainedLabels G H h g d = b d.snd :=
  hb ((SimpleGraph.Hom.ofLE h).mapDart d)

/-- The actual linear trivialization for the retained node equations uses
the original vertex units, including when the remaining graph is a forest. -/
def retainedMatchingLinearEquiv (b : V → kˣ)
    (hb : ∀ d : G.Dart, b d.fst * g d = b d.snd) :
    matchingSections H R (retainedEvaluations G H h R ev) (retainedLabels G H h g)
      ≃ₗ[matchingRing H R (retainedEvaluations G H h R ev)]
        matchingRing H R (retainedEvaluations G H h R ev) :=
  matchingLinearEquiv H R (retainedEvaluations G H h R ev) (retainedLabels G H h g) b
    (retained_vertex_equation G H h g b hb)

/-- Omitting node equations commutes with the original matching
trivialization, as equality of the original component values. -/
theorem retainedMatchingLinearEquiv_natural (b : V → kˣ)
    (hb : ∀ d : G.Dart, b d.fst * g d = b d.snd)
    (s : matchingSections G R ev g) :
    retainedMatchingLinearEquiv G H h R ev g b hb
        (matchingSectionsForget G H h R ev g s) =
      matchingRingForget G H h R ev (matchingLinearEquiv G R ev g b hb s) := rfl

/-- A single original tree potential trivializes every retained-node
module; no new root is chosen for disconnected pieces. -/
def treeRetainedMatchingLinearEquiv (hG : G.IsTree)
    (hreverse : ∀ d : G.Dart, g d.symm = (g d)⁻¹) (root : V) :
    matchingSections H R (retainedEvaluations G H h R ev) (retainedLabels G H h g)
      ≃ₗ[matchingRing H R (retainedEvaluations G H h R ev)]
        matchingRing H R (retainedEvaluations G H h R ev) :=
  retainedMatchingLinearEquiv G H h R ev g
    (KltDP.Combinatorics.treePotential hG g root)
    (fun d => (KltDP.Combinatorics.treePotential_edge hG g hreverse root d.adj).symm)

end KltDP.Geometry.RationalTreePicard
