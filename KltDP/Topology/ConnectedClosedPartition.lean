import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Connected components of a finite connected closed partition

A finite disjoint closed cover is clopen. If every block is nonempty and
connected, the maximal connected subset containing any point is exactly
its block. Choosing a point of each block therefore gives a bijection with
the original ConnectedComponents quotient and the required equivalence.

Current Mathlib has ConnectedComponents.equivOfIsClopenOfIsConnected. This
adapter specializes that result to a finite closed cover using only the
pinned clopen and connected-component APIs, without importing its newer
general quotient-decomposition infrastructure.
-/

noncomputable section

open Set

universe u v

namespace KltDP.Topology.ConnectedClosedPartition

variable {X : Type u} [TopologicalSpace X] {I : Type v}
  (Z : I → Set X)

section Clopen

variable [Finite I] (hclosed : ∀ i, IsClosed (Z i))
  (hdisj : Pairwise (fun i j => Disjoint (Z i) (Z j)))
  (hcover : ⋃ i, Z i = Set.univ)

include hclosed hdisj hcover

/-- Every block of a finite disjoint closed cover is also open. -/
theorem isClopen (i : I) : IsClopen (Z i) := by
  classical
  have hcompl : (Z i)ᶜ = ⋃ j : {j : I // j ≠ i}, Z j.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.mp hcover x
      have hji : j ≠ i := by
        intro hji
        subst j
        exact hx hj
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      intro hxi
      exact Set.disjoint_left.mp (hdisj j.property) hj hxi
  refine ⟨hclosed i, isClosed_compl_iff.mp ?_⟩
  rw [hcompl]
  exact isClosed_iUnion_of_finite fun j => hclosed j.val

/-- A connected block is exactly the original connected component of each of its points. -/
theorem connectedComponent_eq (hconn : ∀ i, IsConnected (Z i))
    (i : I) {x : X} (hx : x ∈ Z i) : connectedComponent x = Z i :=
  ((isClopen Z hclosed hdisj hcover i).connectedComponent_subset hx).antisymm
    ((hconn i).subset_connectedComponent hx)

end Clopen

variable (hclosed : ∀ i, IsClosed (Z i)) (hconn : ∀ i, IsConnected (Z i))

/-- The actual connected-component quotient class of a point in a block. -/
def componentOf (i : I) : ConnectedComponents X :=
  ConnectedComponents.mk (hconn i).nonempty.choose

include hconn

/-- The chosen component class is independent of the choice of point in the block. -/
theorem componentOf_eq_mk (i : I) (x : X) (hx : x ∈ Z i) :
    componentOf Z hconn i = ConnectedComponents.mk x :=
  ConnectedComponents.coe_eq_coe'.mpr
    ((hconn i).subset_connectedComponent hx (hconn i).nonempty.choose_spec)

variable [Finite I]
  (hdisj : Pairwise (fun i j => Disjoint (Z i) (Z j)))
  (hcover : ⋃ i, Z i = Set.univ)

include hclosed hdisj hcover

/-- The actual block-to-component map is both injective and surjective. -/
theorem componentOf_bijective : Function.Bijective (componentOf Z hconn) := by
  classical
  constructor
  · intro i j hij
    have hcomponents : connectedComponent (hconn i).nonempty.choose =
        connectedComponent (hconn j).nonempty.choose := ConnectedComponents.coe_eq_coe.mp hij
    have hblocks : Z i = Z j :=
      (connectedComponent_eq Z hclosed hdisj hcover hconn i (hconn i).nonempty.choose_spec).symm.trans
        (hcomponents.trans
          (connectedComponent_eq Z hclosed hdisj hcover hconn j (hconn j).nonempty.choose_spec))
    by_contra hne
    have hmem : (hconn i).nonempty.choose ∈ Z j := hblocks ▸ (hconn i).nonempty.choose_spec
    exact Set.disjoint_left.mp (hdisj hne) (hconn i).nonempty.choose_spec hmem
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hcover x
    exact ⟨i, componentOf_eq_mk Z hconn i x hi⟩

/-- A finite partition by nonempty connected closed subsets indexes the actual connected components. -/
def connectedComponentsEquiv : ConnectedComponents X ≃ I :=
  (Equiv.ofBijective (componentOf Z hconn)
    (componentOf_bijective Z hclosed hconn hdisj hcover)).symm

/-- The equivalence sends the actual quotient class of a point to its original block index. -/
theorem connectedComponentsEquiv_mk (i : I) (x : X) (hx : x ∈ Z i) :
    connectedComponentsEquiv Z hclosed hconn hdisj hcover (ConnectedComponents.mk x) = i := by
  have h := (connectedComponentsEquiv Z hclosed hconn hdisj hcover).apply_symm_apply i
  change connectedComponentsEquiv Z hclosed hconn hdisj hcover (componentOf Z hconn i) = i at h
  rw [componentOf_eq_mk Z hconn i x hx] at h
  exact h

/-- The original connected-component quotient is finite. -/
theorem finite_connectedComponents : Finite (ConnectedComponents X) :=
  Finite.of_equiv I (connectedComponentsEquiv Z hclosed hconn hdisj hcover).symm

/-- The exact number of original connected components is the number of partition blocks. -/
theorem natCard_connectedComponents : Nat.card (ConnectedComponents X) = Nat.card I :=
  Nat.card_congr (connectedComponentsEquiv Z hclosed hconn hdisj hcover)

end KltDP.Topology.ConnectedClosedPartition
