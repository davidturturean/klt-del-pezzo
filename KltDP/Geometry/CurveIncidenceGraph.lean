import KltDP.Geometry.PrimeDivisor
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Topology.Connected.Basic

/-!
# Incidence graphs of actual prime curves

The graph is constructed from nonempty intersections of the actual closed
curve carriers. For a finite family its connectedness is equivalent to
connectedness of their union. A morphism contracting each curve to a point
is constant on every graph component, so curves contracted to different
points cannot lie in the same component.

No resolution, SNC condition, intersection number, acyclicity, singular
image, or correspondence with all fibers is assumed or established here.
The fiber corollary retains the actual fiber-cover and connectedness
obligations as explicit geometric inputs.
-/

noncomputable section

open Set SimpleGraph AlgebraicGeometry CategoryTheory

universe u v w

namespace KltDP.Topology

variable {α : Type u} {ι : Type v}

/-- The graph of nonempty intersections, with loops omitted. -/
def incidenceGraph (s : ι → Set α) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (s i ∩ s j).Nonempty
  symm := by
    rintro i j ⟨hij, x, hxi, hxj⟩
    exact ⟨hij.symm, x, hxj, hxi⟩
  loopless := fun i hi => hi.1 rfl

theorem incidenceGraph_reachable_of_inter (s : ι → Set α) {i j : ι}
    (h : (s i ∩ s j).Nonempty) : (incidenceGraph s).Reachable i j := by
  by_cases hij : i = j
  · subst j
    exact .refl i
  · exact SimpleGraph.Adj.reachable (show (incidenceGraph s).Adj i j from ⟨hij, h⟩)

variable [TopologicalSpace α]

/-- Graph paths join connected pieces into a connected union. This
direction does not require finiteness or closedness. -/
theorem incidenceGraph_connected_union (s : ι → Set α)
    (hs : ∀ i, IsConnected (s i)) (hG : (incidenceGraph s).Connected) :
    IsConnected (⋃ i, s i) := by
  letI : Nonempty ι := hG.nonempty
  apply IsConnected.iUnion_of_reflTransGen hs
  intro i j
  exact Relation.ReflTransGen.mono (r := (incidenceGraph s).Adj)
    (fun _ _ h => h.2)
    (((incidenceGraph s).reachable_iff_reflTransGen i j).mp (hG i j))

/-- A connected finite union of nonempty closed sets cannot split into
two collections with no intersections between them. No connectedness
of the individual sets is needed in this direction. -/
theorem incidenceGraph_preconnected_of_union [Finite ι] (s : ι → Set α)
    (hclosed : ∀ i, IsClosed (s i)) (hne : ∀ i, (s i).Nonempty)
    (hunion : IsPreconnected (⋃ i, s i)) : (incidenceGraph s).Preconnected := by
  classical
  intro i j
  by_contra hij
  let S : Set ι := {k | (incidenceGraph s).Reachable i k}
  let U : Set α := ⋃ k ∈ S, s k
  let W : Set α := ⋃ k ∈ Sᶜ, s k
  have hU : IsClosed U := (Set.toFinite S).isClosed_biUnion (fun k _ => hclosed k)
  have hW : IsClosed W := (Set.toFinite Sᶜ).isClosed_biUnion (fun k _ => hclosed k)
  have hcover : (⋃ k, s k) ⊆ U ∪ W := by
    intro x hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    by_cases hk : k ∈ S
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)
  obtain ⟨a, ha⟩ := hne i
  obtain ⟨b, hb⟩ := hne j
  have hiS : i ∈ S := SimpleGraph.Reachable.refl i
  have hjS : j ∈ Sᶜ := hij
  have hUne : ((⋃ k, s k) ∩ U).Nonempty :=
    ⟨a, Set.mem_iUnion.mpr ⟨i, ha⟩, Set.mem_iUnion₂.mpr ⟨i, hiS, ha⟩⟩
  have hWne : ((⋃ k, s k) ∩ W).Nonempty :=
    ⟨b, Set.mem_iUnion.mpr ⟨j, hb⟩, Set.mem_iUnion₂.mpr ⟨j, hjS, hb⟩⟩
  obtain ⟨x, _, hxU, hxW⟩ :=
    isPreconnected_closed_iff.mp hunion U W hU hW hcover hUne hWne
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxU
  obtain ⟨l, hl, hxl⟩ := Set.mem_iUnion₂.mp hxW
  have hik : (incidenceGraph s).Reachable i k := hk
  exact hl (hik.trans (incidenceGraph_reachable_of_inter s ⟨x, hxk, hxl⟩))

/-- Connectedness of a finite union of nonempty connected closed pieces
is exactly connectedness of its actual intersection graph. -/
theorem incidenceGraph_connected_iff [Finite ι] (s : ι → Set α)
    (hclosed : ∀ i, IsClosed (s i)) (hs : ∀ i, IsConnected (s i)) :
    (incidenceGraph s).Connected ↔ IsConnected (⋃ i, s i) := by
  constructor
  · exact incidenceGraph_connected_union s hs
  · intro h
    obtain ⟨x, hx⟩ := h.nonempty
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
    letI : Nonempty ι := ⟨i⟩
    exact ⟨incidenceGraph_preconnected_of_union s hclosed
      (fun i => (hs i).nonempty) h.isPreconnected⟩

end KltDP.Topology

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
  {ι : Type v}

/-- Incidence of the actual carriers of an indexed prime-curve family.
No matrix or edge list is supplied separately. -/
def curveIncidenceGraph (curves : ι → X.PrimeCurve) : SimpleGraph ι :=
  KltDP.Topology.incidenceGraph (fun i => (curves i : Set X.toScheme))

theorem curveIncidenceGraph_connected_iff [Finite ι] (curves : ι → X.PrimeCurve) :
    (curveIncidenceGraph curves).Connected ↔
      IsConnected (⋃ i, (curves i : Set X.toScheme)) :=
  KltDP.Topology.incidenceGraph_connected_iff _ (fun i => (curves i).isClosed)
    (fun i => (curves i).isIrreducible.isConnected)

/-- A single actual prime curve gives a nonempty connected graph. -/
theorem curveIncidenceGraph_singleton_connected (C : X.PrimeCurve) :
    (curveIncidenceGraph (fun _ : Unit => C)).Connected := by
  apply (curveIncidenceGraph_connected_iff (fun _ : Unit => C)).mpr
  simpa only [Set.iUnion_const] using C.isIrreducible.isConnected

/-- Actual curve components covering a connected set-theoretic fiber
have a connected incidence graph. The fiber and the cover are geometric
inputs; graph connectedness is the derived conclusion. -/
theorem curveIncidenceGraph_connected_of_fiber [Finite ι]
    (curves : ι → X.PrimeCurve) {Y : Scheme.{u}} (f : X.toScheme ⟶ Y) (y : Y)
    (hcover : (⋃ i, (curves i : Set X.toScheme)) = f.base ⁻¹' {y})
    (hconnected : IsConnected (f.base ⁻¹' {y})) :
    (curveIncidenceGraph curves).Connected := by
  apply (curveIncidenceGraph_connected_iff curves).mpr
  rw [hcover]
  exact hconnected

/-- If an actual morphism contracts each curve to the specified point,
every path in the actual incidence graph has the same image point. -/
theorem contracted_point_eq_of_curve_reachable
    (curves : ι → X.PrimeCurve) {Y : Scheme.{u}} (f : X.toScheme ⟶ Y)
    (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i)
    {i j : ι} (hpath : (curveIncidenceGraph curves).Reachable i j) :
    point i = point j := by
  obtain ⟨p⟩ := hpath
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
      obtain ⟨x, hxa, hxb⟩ := hab.2
      exact ((hcontract a x hxa).symm.trans (hcontract b x hxb)).trans ih

/-- Contracted curves above distinct actual points belong to different
graph components. -/
theorem curve_not_reachable_of_contracted_points_ne
    (curves : ι → X.PrimeCurve) {Y : Scheme.{u}} (f : X.toScheme ⟶ Y)
    (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i)
    {i j : ι} (hne : point i ≠ point j) :
    ¬ (curveIncidenceGraph curves).Reachable i j :=
  fun h => hne (contracted_point_eq_of_curve_reachable curves f point hcontract h)

end KltDP.Geometry.NormalProjectiveSurface
