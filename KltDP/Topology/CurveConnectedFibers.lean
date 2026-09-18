import KltDP.Topology.DimensionOneClosedSubsets
import Mathlib.Topology.Separation.Connected

/-!
Connected fibers of a nonconstant closed map out of an irreducible
Noetherian curve are singletons. At a closed target point the original
fiber is a finite set of closed points. Above a nonclosed target point,
every source point has dense closure and hence is the same point by T0.
-/

set_option autoImplicit false

noncomputable section
open TopologicalSpace

namespace KltDP.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [IrreducibleSpace X] [T0Space X] [NoetherianSpace X]

/-- A nonclosed point on the original irreducible curve has dense closure. -/
theorem closure_singleton_eq_univ_of_not_isClosed
    (hdim : topologicalKrullDim X ≤ 1) (x : X)
    (hx : ¬ IsClosed ({x} : Set X)) : closure ({x} : Set X) = Set.univ := by
  by_contra hne
  obtain ⟨z, hz⟩ := eq_singleton_of_isIrreducible_of_isClosed_of_ne_univ
    hdim isIrreducible_singleton.closure isClosed_closure hne
  have hxz : x = z := by
    have hm : x ∈ closure ({x} : Set X) := subset_closure (Set.mem_singleton x)
    rw [hz, Set.mem_singleton_iff] at hm
    exact hm
  subst z
  exact hx (hz ▸ isClosed_closure)

/-- The actual topological fibers are singletons whenever they are connected. -/
theorem bijective_of_closed_nonconstant_of_connected_fibers
    (hdim : topologicalKrullDim X ≤ 1) (f : X → Y)
    (hcont : Continuous f) (hclosed : IsClosedMap f)
    (hnonconstant : ¬ ∃ y : Y, ∀ x : X, f x = y)
    (hconnected : ∀ y : Y, IsConnected (f ⁻¹' {y})) :
    Function.Bijective f := by
  have hfiber (y : Y) : (f ⁻¹' {y}).Subsingleton := by
    by_cases hy : IsClosed ({y} : Set Y)
    · have hne : f ⁻¹' {y} ≠ Set.univ := by
        intro heq
        apply hnonconstant
        refine ⟨y, fun x => ?_⟩
        have hx : x ∈ f ⁻¹' {y} := heq ▸ Set.mem_univ x
        exact hx
      obtain ⟨hfinite, hpoints⟩ :=
        finite_and_isClosed_singleton_of_isClosed_of_ne_univ hdim
          (hy.preimage hcont) hne
      letI : Finite (f ⁻¹' {y}) := hfinite.to_subtype
      letI : DiscreteTopology (f ⁻¹' {y}) :=
        DiscreteTopology.of_finite_of_isClosed_singleton fun x => by
          have hx : IsClosed ((Subtype.val : (f ⁻¹' {y}) → X) ⁻¹' {(x : X)}) :=
            (hpoints x x.property).preimage continuous_subtype_val
          convert hx using 1
          ext z
          simp only [Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
      letI : PreconnectedSpace (f ⁻¹' {y}) :=
        Subtype.preconnectedSpace (hconnected y).isPreconnected
      letI : Subsingleton (f ⁻¹' {y}) := PreconnectedSpace.trivial_of_discrete
      intro x hx z hz
      exact congrArg Subtype.val (Subsingleton.elim
        (⟨x, hx⟩ : f ⁻¹' {y}) (⟨z, hz⟩ : f ⁻¹' {y}))
    · have hdense (x : X) (hx : x ∈ f ⁻¹' {y}) :
          closure ({x} : Set X) = Set.univ := by
        apply closure_singleton_eq_univ_of_not_isClosed hdim x
        intro hxc
        apply hy
        have him := hclosed ({x} : Set X) hxc
        have hfx : f x = y := hx
        simpa only [Set.image_singleton, hfx] using him
      intro x hx z hz
      exact (inseparable_iff_closure_eq.mpr ((hdense x hx).trans (hdense z hz).symm)).eq
  constructor
  · intro x z hxz
    exact hfiber (f x) rfl hxz.symm
  · intro y
    obtain ⟨x, hx⟩ := (hconnected y).nonempty
    exact ⟨x, hx⟩

#check KltDP.Topology.bijective_of_closed_nonconstant_of_connected_fibers
#print axioms KltDP.Topology.bijective_of_closed_nonconstant_of_connected_fibers

end KltDP.Topology
