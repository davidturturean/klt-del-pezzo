import KltDP.Geometry.CurveIncidenceGraph
import KltDP.Geometry.PrimeCurvePairingSupport

/-!
# Actual incidence edges and the original intersection pairing

For distinct actual prime curves on a regular surface, an incidence edge
is equivalent to positive original intersection pairing. Different graph
components are orthogonal for that same pairing. This supplies the matrix
support of the actual graph without assuming a separate adjacency formula.
-/

noncomputable section

open AlgebraicGeometry

universe u v

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  {I : Type v} (curves : I → X.PrimeCurve) (hinj : Function.Injective curves)

include hinj in
/-- An edge of the original carrier-incidence graph is detected by the
positive intersection number of the same labelled prime curves. -/
theorem curveIncidenceGraph_adj_iff_pairing_pos {i j : I} :
    (curveIncidenceGraph curves).Adj i j ↔
      i ≠ j ∧ 0 < X.intersectionPairing hregular
        (X.primeCurveCartier hregular (curves i))
        (X.primeCurveCartier hregular (curves j)) := by
  change (i ≠ j ∧ ((curves i : Set X.toScheme) ∩
    (curves j : Set X.toScheme)).Nonempty) ↔ _
  constructor
  · rintro ⟨hij, hinter⟩
    have hne : curves i ≠ curves j := fun heq => hij (hinj heq)
    have hnonneg := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg
      X hregular (curves i) (curves j) hne
    have hzero : X.intersectionPairing hregular
        (X.primeCurveCartier hregular (curves i))
        (X.primeCurveCartier hregular (curves j)) ≠ 0 := by
      intro hz
      exact hinter.not_disjoint
        ((PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
          X hregular (curves i) (curves j) hne).mp hz)
    exact ⟨hij, lt_of_le_of_ne hnonneg hzero.symm⟩
  · rintro ⟨hij, hpos⟩
    refine ⟨hij, Set.not_disjoint_iff_nonempty_inter.mp ?_⟩
    intro hd
    have hzero := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      X hregular (curves i) (curves j) (fun heq => hij (hinj heq))).mpr hd
    exact (ne_of_gt hpos) hzero

include hinj in
/-- Curves in different actual graph components have zero original pairing. -/
theorem pairing_eq_zero_of_not_reachable {i j : I}
    (hpath : ¬ (curveIncidenceGraph curves).Reachable i j) :
    X.intersectionPairing hregular
      (X.primeCurveCartier hregular (curves i))
      (X.primeCurveCartier hregular (curves j)) = 0 := by
  have hij : i ≠ j := by
    rintro rfl
    exact hpath (.refl i)
  apply (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
    X hregular (curves i) (curves j) (fun heq => hij (hinj heq))).mpr
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact hpath (KltDP.Topology.incidenceGraph_reachable_of_inter
    (fun l => (curves l : Set X.toScheme)) ⟨x, hxi, hxj⟩)

include hinj in
/-- The pairing matrix is block diagonal for the constructed graph-component
partition, with no independent block-decomposition hypothesis. -/
theorem pairing_eq_zero_of_components_ne {i j : I}
    (hcomponents : (curveIncidenceGraph curves).connectedComponentMk i ≠
      (curveIncidenceGraph curves).connectedComponentMk j) :
    X.intersectionPairing hregular
      (X.primeCurveCartier hregular (curves i))
      (X.primeCurveCartier hregular (curves j)) = 0 :=
  pairing_eq_zero_of_not_reachable X hregular curves hinj
    (fun hpath => hcomponents (SimpleGraph.ConnectedComponent.sound hpath))

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.curveIncidenceGraph_adj_iff_pairing_pos
