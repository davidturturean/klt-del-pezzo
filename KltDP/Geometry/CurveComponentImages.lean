import KltDP.Geometry.CurveIncidenceGraph
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Card

/-!
# Actual curve components and their contracted image points

For a finite family of actual prime curves contracted by a scheme
morphism, connectedness of the covered fibers makes graph reachability
equivalent to equality of the actual image points. The existing quotient
first-isomorphism theorem then gives the component/image bijection and
the count equality. No component correspondence or count is an input.

The fiber-cover and connectedness hypotheses are geometric obligations
for a later resolution or Stein-contraction use site. This module does
not construct that morphism or identify its image points as singular.
-/

noncomputable section

open Set SimpleGraph AlgebraicGeometry CategoryTheory

universe u v

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
  {ι : Type v} {Y : Scheme.{u}}

/-- Restricting an actual curve family gives an actual graph homomorphism
to the full incidence graph. -/
def curveIncidenceSubtypeHom (curves : ι → X.PrimeCurve) (s : Set ι) :
    curveIncidenceGraph (fun i : s => curves i.val) →g curveIncidenceGraph curves where
  toFun := Subtype.val
  map_rel' := by
    intro i j hij
    exact ⟨fun h => hij.1 (Subtype.ext h), hij.2⟩

/-- The labels of contracted curves are precisely the actual image of
their union. Nonemptiness of each prime curve supplies the reverse inclusion. -/
theorem contracted_points_range_eq_image
    (curves : ι → X.PrimeCurve) (f : X.toScheme ⟶ Y) (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i) :
    Set.range point = f.base '' (⋃ i, (curves i : Set X.toScheme)) := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := (curves i).nonempty
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, hcontract i x hx⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, (hcontract i x hxi).symm⟩

/-- A fiber covered by the total curve union is exactly the union of
the curves with that image point. No graph connectedness is used. -/
theorem contracted_fiber_eq_curve_union
    (curves : ι → X.PrimeCurve) (f : X.toScheme ⟶ Y) (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i)
    (y : Y)
    (hcover : f.base ⁻¹' {y} ⊆ ⋃ i, (curves i : Set X.toScheme)) :
    (⋃ i : {i // point i = y}, (curves i.val : Set X.toScheme)) = f.base ⁻¹' {y} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    change f.base x = y
    exact (hcontract i.val x hxi).trans i.property
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hx)
    have hiy : point i = y := (hcontract i x hxi).symm.trans hx
    exact Set.mem_iUnion.mpr ⟨⟨i, hiy⟩, hxi⟩

section FiniteFamily

variable [Finite ι]

/-- The actual graph-component type is finite because it is a quotient
of the finite curve index type. -/
theorem curve_incidence_components_finite (curves : ι → X.PrimeCurve) :
    Finite (curveIncidenceGraph curves).ConnectedComponent :=
  Quot.finite _

/-- Pointwise contraction makes the actual image of the curve union a
finite set of scheme points. -/
theorem contracted_curve_union_image_finite
    (curves : ι → X.PrimeCurve) (f : X.toScheme ⟶ Y) (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i) :
    (f.base '' (⋃ i, (curves i : Set X.toScheme))).Finite := by
  rw [← contracted_points_range_eq_image curves f point hcontract]
  exact Set.finite_range point

/-- Covered connected actual fibers force all curves with the same
image point to lie in the same actual incidence component. -/
theorem curve_reachable_iff_contracted_points_eq
    (curves : ι → X.PrimeCurve) (f : X.toScheme ⟶ Y) (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i)
    (hcover : ∀ y ∈ Set.range point,
      f.base ⁻¹' {y} ⊆ ⋃ i, (curves i : Set X.toScheme))
    (hconnected : ∀ y ∈ Set.range point, IsConnected (f.base ⁻¹' {y}))
    (i j : ι) :
    (curveIncidenceGraph curves).Reachable i j ↔ point i = point j := by
  constructor
  · exact contracted_point_eq_of_curve_reachable curves f point hcontract
  · intro hij
    let s : Set ι := {l | point l = point i}
    have hi : point i ∈ Set.range point := Set.mem_range_self i
    have hG : (curveIncidenceGraph (fun l : s => curves l.val)).Connected :=
      curveIncidenceGraph_connected_of_fiber (fun l : s => curves l.val) f (point i)
        (contracted_fiber_eq_curve_union curves f point hcontract (point i)
          (hcover (point i) hi))
        (hconnected (point i) hi)
    exact (hG ⟨i, rfl⟩ ⟨j, hij.symm⟩).map (curveIncidenceSubtypeHom curves s)

/-- The actual incidence components biject with the distinct contracted
image points. The only quotient machinery is Mathlib's existing
congruence and kernel-to-range equivalence. -/
def curveComponentImageEquiv
    (curves : ι → X.PrimeCurve) (f : X.toScheme ⟶ Y) (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i)
    (hcover : ∀ y ∈ Set.range point,
      f.base ⁻¹' {y} ⊆ ⋃ i, (curves i : Set X.toScheme))
    (hconnected : ∀ y ∈ Set.range point, IsConnected (f.base ⁻¹' {y})) :
    (curveIncidenceGraph curves).ConnectedComponent ≃ Set.range point :=
  (Quotient.congrRight (r := (curveIncidenceGraph curves).reachableSetoid)
    (r' := Setoid.ker point)
    (curve_reachable_iff_contracted_points_eq curves f point hcontract hcover hconnected)).trans
      (Setoid.quotientKerEquivRange point)

/-- The bijection sends the component of an actual curve to that curve's
actual contracted image point. -/
@[simp]
theorem curveComponentImageEquiv_mk
    (curves : ι → X.PrimeCurve) (f : X.toScheme ⟶ Y) (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i)
    (hcover : ∀ y ∈ Set.range point,
      f.base ⁻¹' {y} ⊆ ⋃ i, (curves i : Set X.toScheme))
    (hconnected : ∀ y ∈ Set.range point, IsConnected (f.base ⁻¹' {y}))
    (i : ι) :
    curveComponentImageEquiv curves f point hcontract hcover hconnected
      ((curveIncidenceGraph curves).connectedComponentMk i) =
        ⟨point i, Set.mem_range_self i⟩ := rfl

/-- Equality of component count and the number of distinct image points,
derived from the actual bijection. The finite-family hypothesis rules out
the infinite-type zero convention for natural cardinalities. -/
theorem curve_component_card_eq_contracted_points_ncard
    (curves : ι → X.PrimeCurve) (f : X.toScheme ⟶ Y) (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i)
    (hcover : ∀ y ∈ Set.range point,
      f.base ⁻¹' {y} ⊆ ⋃ i, (curves i : Set X.toScheme))
    (hconnected : ∀ y ∈ Set.range point, IsConnected (f.base ⁻¹' {y})) :
    Nat.card (curveIncidenceGraph curves).ConnectedComponent = (Set.range point).ncard := by
  rw [← Set.Nat.card_coe_set_eq]
  exact Nat.card_congr (curveComponentImageEquiv curves f point hcontract hcover hconnected)

/-- The same count equality expressed directly using the actual image
of the curve union under the scheme morphism. -/
theorem curve_component_card_eq_image_union_ncard
    (curves : ι → X.PrimeCurve) (f : X.toScheme ⟶ Y) (point : ι → Y)
    (hcontract : ∀ i, ∀ x ∈ (curves i : Set X.toScheme), f.base x = point i)
    (hcover : ∀ y ∈ Set.range point,
      f.base ⁻¹' {y} ⊆ ⋃ i, (curves i : Set X.toScheme))
    (hconnected : ∀ y ∈ Set.range point, IsConnected (f.base ⁻¹' {y})) :
    Nat.card (curveIncidenceGraph curves).ConnectedComponent =
      (f.base '' (⋃ i, (curves i : Set X.toScheme))).ncard := by
  rw [← contracted_points_range_eq_image curves f point hcontract]
  exact curve_component_card_eq_contracted_points_ncard curves f point hcontract hcover hconnected

end FiniteFamily

end KltDP.Geometry.NormalProjectiveSurface
