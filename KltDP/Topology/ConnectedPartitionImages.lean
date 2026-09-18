import KltDP.Topology.ConnectedClosedPartition
import Mathlib.Data.Set.Card

/-!
Distinct blocks of a finite closed partition have distinct constant images
when the original point fibers are preconnected. The existing clopen-block
lemma supplies the separation argument. No image-point bijection or count
is an input; both are derived from the original function and partition.
-/

noncomputable section
open Set
universe u v w

namespace KltDP.Topology.ConnectedPartitionImages

variable {X : Type u} [TopologicalSpace X] {Y : Type v} {I : Type w}
  [Finite I] (Z : I → Set X)
  (hclosed : ∀ i, IsClosed (Z i)) (hne : ∀ i, (Z i).Nonempty)
  (hdisj : Pairwise (fun i j => Disjoint (Z i) (Z j)))
  (hcover : ⋃ i, Z i = Set.univ)
  (f : X → Y) (point : I → Y)
  (hconstant : ∀ i, ∀ x ∈ Z i, f x = point i)
  (hfibers : ∀ y, IsPreconnected (f ⁻¹' {y}))

include hclosed hne hdisj hcover hconstant hfibers in
/-- Connected original fibers separate the actual constant values of
distinct nonempty blocks. -/
theorem point_injective : Function.Injective point := by
  intro i j hij
  obtain ⟨x, hx⟩ := hne i
  obtain ⟨z, hz⟩ := hne j
  have hxf : x ∈ f ⁻¹' {point i} := hconstant i x hx
  have hzf : z ∈ f ⁻¹' {point i} := (hconstant j z hz).trans hij.symm
  have hzx : z ∈ connectedComponent x :=
    (hfibers (point i)).subset_connectedComponent hxf hzf
  have hzi : z ∈ Z i :=
    (ConnectedClosedPartition.isClopen Z hclosed hdisj hcover i).connectedComponent_subset hx hzx
  by_contra hneij
  exact Set.disjoint_left.mp (hdisj hneij) hzi hz

include hne hcover hconstant in
/-- The block values are exactly the actual image of the original function. -/
theorem range_point_eq_range : Set.range point = Set.range f := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hne i
    exact ⟨x, hconstant i x hx⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hcover x
    exact ⟨i, (hconstant i x hi).symm⟩

/-- The finite block type bijects with the original image-point range. -/
def blockImageEquiv : I ≃ Set.range point :=
  Equiv.ofInjective point
    (point_injective Z hclosed hne hdisj hcover f point hconstant hfibers)

include hclosed hne hdisj hcover hconstant hfibers in
/-- Counting actual distinct image points gives exactly the finite block count. -/
theorem natCard_range : Nat.card (Set.range f) = Nat.card I := by
  rw [← range_point_eq_range Z hne hcover f point hconstant]
  exact (Nat.card_congr (blockImageEquiv Z hclosed hne hdisj hcover f point hconstant hfibers)).symm

include hne hcover hconstant in
/-- The original image is finite because it is the image of the finite block type. -/
theorem range_finite : (Set.range f).Finite := by
  rw [← range_point_eq_range Z hne hcover f point hconstant]
  exact Set.finite_range point

end KltDP.Topology.ConnectedPartitionImages
