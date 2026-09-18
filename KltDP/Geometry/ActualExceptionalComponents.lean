import KltDP.Geometry.ActualExceptionalLocus
import KltDP.Topology.ConnectedFiberComponentEquiv
import KltDP.Geometry.SurfaceSingularCountOnIsomorphismOpen

/-!
# Actual exceptional connected components and their original image points

The original proper map sends the whole union of contracted prime curves
onto a finite set of closed points. The proved fiber exhaustion says that
its restricted fibers are exactly its original fibers. Their connectedness
therefore makes the original map induce a bijection on connected components.

For a regular source and an isomorphic original structure-sheaf pushforward,
the number of actual singular target points is at most this component count.
Equality with the singular-point count still requires the minimality argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ActualExceptionalLocus

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]

/-- A point in the actual contracted image is closed: it is the entire
proper image of one original prime curve. -/
theorem imagePoint_isClosed (y : imagePoints π) :
    IsClosed ({y.val} : Set X.toScheme) := by
  obtain ⟨x, hx, hxy⟩ := y.property
  obtain ⟨C, hC, hxC⟩ := (mem_primeSupport π x).mp hx
  obtain ⟨z, hz⟩ := hC
  have hxz : π.base x = z := by
    have hmem := Set.mem_image_of_mem π.base hxC
    rwa [hz] at hmem
  have hyz : y.val = z := hxy.symm.trans hxz
  rw [hyz]
  have hclosed := π.isClosedMap (C : Set S.toScheme) C.isClosed
  rwa [hz] at hclosed

private theorem imagePoints_t1 : T1Space (imagePoints π) := by
  constructor
  intro y
  convert (imagePoint_isClosed π y).preimage
    (continuous_subtype_val : Continuous ((↑) : imagePoints π → X.toScheme)) using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]

variable (hbir : IsBirationalScheme π)

include hbir in
/-- The actual finite image has its induced discrete topology. -/
theorem imagePoints_discrete : DiscreteTopology (imagePoints π) := by
  letI : Finite (imagePoints π) := (imagePoints_finite π hbir).to_subtype
  letI : T1Space (imagePoints π) := imagePoints_t1 π
  infer_instance

/-- The restriction and corestriction of the original morphism on points. -/
def imageMap : primeSupport π → imagePoints π :=
  fun x => ⟨π.base x.val, x.val, x.property, rfl⟩

theorem imageMap_continuous : Continuous (imageMap π) :=
  (π.continuous.comp continuous_subtype_val).subtype_mk _

variable [IsAlgClosed k]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hconnected : ∀ y : X.toScheme, IsConnected (π.base ⁻¹' {y}))

include hbir hπ hconnected in
/-- The actual restricted fiber, embedded back into the original surface,
is the whole original point fiber, including every point of every component. -/
theorem imageMap_fiber_image (y : imagePoints π) :
    ((↑) : primeSupport π → S.toScheme) '' (imageMap π ⁻¹' {y}) =
      π.base ⁻¹' {y.val} := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact congrArg Subtype.val hz
  · intro x hx
    have hs : x ∈ primeSupport π := by
      rw [← preimage_image_primeSupport π hbir hπ hconnected]
      change π.base x ∈ imagePoints π
      rw [show π.base x = y.val from hx]
      exact y.property
    exact ⟨⟨x, hs⟩, Subtype.ext hx, rfl⟩

include hbir hπ hconnected in
/-- The connectedness of the original fibers is preserved by the actual
restriction to the exceptional support; no component partition is assumed. -/
theorem imageMap_fibers_connected (y : imagePoints π) :
    IsConnected (imageMap π ⁻¹' {y}) := by
  have himage : IsConnected
      (((↑) : primeSupport π → S.toScheme) '' (imageMap π ⁻¹' {y})) := by
    rw [imageMap_fiber_image π hbir hπ hconnected]
    exact hconnected y.val
  exact ⟨Set.image_nonempty.mp himage.nonempty,
    _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp himage.isPreconnected⟩

/-- The original map induces a bijection from actual exceptional connected
components to its actual contracted image points. -/
def componentImageEquiv : ConnectedComponents (primeSupport π) ≃ imagePoints π := by
  letI : DiscreteTopology (imagePoints π) := imagePoints_discrete π hbir
  exact KltDP.Topology.ConnectedFiberComponentEquiv.equiv (imageMap π)
    (imageMap_continuous π) (imageMap_fibers_connected π hbir hπ hconnected)

@[simp] theorem componentImageEquiv_apply_coe (x : primeSupport π) :
    componentImageEquiv π hbir hπ hconnected (x : ConnectedComponents (primeSupport π)) =
      imageMap π x := rfl

include hbir hπ hconnected in
/-- The component type is finite before its natural cardinality is used. -/
theorem finite_connectedComponents : Finite (ConnectedComponents (primeSupport π)) := by
  letI : Finite (imagePoints π) := (imagePoints_finite π hbir).to_subtype
  exact Finite.of_equiv (imagePoints π) (componentImageEquiv π hbir hπ hconnected).symm

include hbir hπ hconnected in
/-- This counts actual connected exceptional blocks, rather than their
individual prime components. -/
theorem component_count :
    Nat.card (ConnectedComponents (primeSupport π)) = (imagePoints π).ncard := by
  rw [← Set.Nat.card_coe_set_eq]
  exact Nat.card_congr (componentImageEquiv π hbir hπ hconnected)

include hbir hπ hconnected in
/-- Actual singular target points are bounded by the actual exceptional
connected-component count. The source is regular and the original map's
structure-sheaf pushforward is an isomorphism. -/
theorem singularPoints_card_le_components [IsIso π.c]
    (hreg : ∀ x : S.toScheme, RegularPoint S.toScheme x) :
    X.singularPoints.card ≤ Nat.card (ConnectedComponents (primeSupport π)) := by
  letI : IsIso (π ∣_ complementOpen π hbir) :=
    isIso_complementOpen π hbir hπ hconnected
  have hfinite : (((complementOpen π hbir : X.toScheme.Opens) : Set X.Point)ᶜ).Finite := by
    change ((imagePoints π)ᶜᶜ).Finite
    rw [compl_compl]
    exact imagePoints_finite π hbir
  have hbound := RegularPointsOnIsomorphismOpen.singularPoints_card_le_natCard_compl
    X π (complementOpen π hbir) hreg hfinite
  calc
    X.singularPoints.card ≤ Nat.card (imagePoints π) := by
      change X.singularPoints.card ≤ Nat.card {x : X.Point // x ∈ ((imagePoints π)ᶜᶜ : Set X.Point)} at hbound
      rw [compl_compl] at hbound
      exact hbound
    _ = Nat.card (ConnectedComponents (primeSupport π)) :=
      (Nat.card_congr (componentImageEquiv π hbir hπ hconnected)).symm

end KltDP.Geometry.ActualExceptionalLocus
