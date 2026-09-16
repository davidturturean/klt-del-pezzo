import KltDP.Geometry.RationalTreePicardComponentPartition
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.KrullDimension

/-!
# Dimension of the original closed component unions

Every irreducible component of the actual closed component-union scheme
is the inverse image of a selected original component. This is proved
using the original generic points and the actual closed immersion.
Restricting that immersion gives a homeomorphism with the original
component, so its topological Krull dimension is unchanged.

A nonempty selection in an equidimensional scheme of dimension one
therefore gives an actual reduced closed subscheme equidimensional of
dimension one. Both the dimension of the whole scheme and the dimensions
of its components are retained; the empty union is not declared to have
dimension one. These are ordinary prerequisites for a future literal
nodal-cut application, with no nodality or intersection conclusion assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u}) [NoetherianSpace X]
  (S : Set ↥(irreducibleComponents X))

/-- Each selected original component is contained in the range of the
actual closed-union inclusion. -/
theorem component_subset_range_componentUnionInclusion
    (C : ↥(irreducibleComponents X)) (hC : C ∈ S) :
    C.1 ⊆ Set.range (componentUnionInclusion X S).base := by
  rw [range_componentUnionInclusion]
  intro x hx
  exact (mem_componentClosedUnion X S x).mpr ⟨C, hC, hx⟩

/-- The original generic point lifts along the actual inclusion. Its
closure is precisely the inverse image of the original component. -/
theorem componentUnionInclusion_preimage_isIrreducible
    (C : ↥(irreducibleComponents X)) (hC : C ∈ S) :
    IsIrreducible ((componentUnionInclusion X S).base ⁻¹' C.1) := by
  have hgeneric := C.2.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents C.1 C.2)
  obtain ⟨y, hy⟩ := component_subset_range_componentUnionInclusion X S C hC hgeneric.mem
  have hclosure : closure ({y} : Set (componentUnionScheme X S)) =
      (componentUnionInclusion X S).base ⁻¹' C.1 := by
    rw [(componentUnionInclusion X S).isEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hy, C.2.1.closure_genericPoint
        (isClosed_of_mem_irreducibleComponents C.1 C.2)]
  rw [← hclosure]
  exact isIrreducible_singleton.closure

/-- Every actual component of the closed union is the inverse image of
a selected original component. No component correspondence is an input. -/
theorem exists_componentUnionComponent_eq_preimage
    (D : ↥(irreducibleComponents (componentUnionScheme X S))) :
    ∃ C : ↥(irreducibleComponents X), C ∈ S ∧
      D.1 = (componentUnionInclusion X S).base ⁻¹' C.1 := by
  have hgeneric := D.2.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents D.1 D.2)
  have hy : (componentUnionInclusion X S).base D.2.1.genericPoint ∈
      componentClosedUnion X S := by
    rw [← SetLike.mem_coe, ← range_componentUnionInclusion]
    exact ⟨_, rfl⟩
  obtain ⟨C, hC, hyC⟩ := (mem_componentClosedUnion X S _).mp hy
  have hDC : D.1 ⊆ (componentUnionInclusion X S).base ⁻¹' C.1 :=
    (hgeneric.mem_closed_set_iff
      ((isClosed_of_mem_irreducibleComponents C.1 C.2).preimage
        (componentUnionInclusion X S).base.hom.continuous)).mp hyC
  exact ⟨C, hC, hDC.antisymm
    (D.2.2 (componentUnionInclusion_preimage_isIrreducible X S C hC) hDC)⟩

/-- The actual image of an original component of the union is a selected
original component of the ambient scheme. -/
theorem exists_componentUnionComponent_image
    (D : ↥(irreducibleComponents (componentUnionScheme X S))) :
    ∃ C : ↥(irreducibleComponents X), C ∈ S ∧
      (componentUnionInclusion X S).base '' D.1 = C.1 := by
  obtain ⟨C, hC, hD⟩ := exists_componentUnionComponent_eq_preimage X S D
  refine ⟨C, hC, ?_⟩
  rw [hD]
  exact Set.image_preimage_eq_of_subset
    (component_subset_range_componentUnionInclusion X S C hC)

/-- The homeomorphism is the restriction of the actual original
closed immersion to the inverse image of a selected component. -/
def componentUnionPreimageHomeomorph
    (C : ↥(irreducibleComponents X)) (hC : C ∈ S) :
    ((componentUnionInclusion X S).base ⁻¹' C.1) ≃ₜ C.1 := by
  let H : Set.MapsTo (componentUnionInclusion X S).base
      ((componentUnionInclusion X S).base ⁻¹' C.1) C.1 := fun _ hx => hx
  apply ((componentUnionInclusion X S).isEmbedding.restrict H).toHomeomorphOfSurjective
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := component_subset_range_componentUnionInclusion X S C hC hx
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change (componentUnionInclusion X S).base y ∈ C.1
    exact hy.symm ▸ hx
  · exact Subtype.ext hy

/-- The restricted homeomorphism preserves the original point in X. -/
@[simp]
theorem componentUnionPreimageHomeomorph_apply
    (C : ↥(irreducibleComponents X)) (hC : C ∈ S)
    (y : (componentUnionInclusion X S).base ⁻¹' C.1) :
    (componentUnionPreimageHomeomorph X S C hC y : X) =
      (componentUnionInclusion X S).base y.1 := rfl

/-- Actual irreducible components of the closed union have the topology
of selected original components, by the proved component correspondence. -/
theorem exists_componentUnionComponent_homeomorph
    (D : ↥(irreducibleComponents (componentUnionScheme X S))) :
    ∃ C : ↥(irreducibleComponents X), C ∈ S ∧ Nonempty (D.1 ≃ₜ C.1) := by
  obtain ⟨C, hC, hD⟩ := exists_componentUnionComponent_eq_preimage X S D
  exact ⟨C, hC, ⟨(Homeomorph.setCongr hD).trans
    (componentUnionPreimageHomeomorph X S C hC)⟩⟩

/-- A common dimension of the selected original components is inherited
by every actual component of their closed-union scheme. -/
theorem componentUnionComponent_topologicalKrullDim (d : WithBot ℕ∞)
    (hdim : ∀ C : ↥(irreducibleComponents X), C ∈ S → topologicalKrullDim C.1 = d)
    (D : ↥(irreducibleComponents (componentUnionScheme X S))) :
    topologicalKrullDim D.1 = d := by
  obtain ⟨C, hC, ⟨e⟩⟩ := exists_componentUnionComponent_homeomorph X S D
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).trans (hdim C hC)

/-- Nonemptiness is obtained from the original selected components, and
fails for the empty selection. -/
theorem componentUnionScheme_nonempty_iff :
    Nonempty (componentUnionScheme X S) ↔ S.Nonempty := by
  constructor
  · rintro ⟨y⟩
    have hy : (componentUnionInclusion X S).base y ∈ componentClosedUnion X S := by
      rw [← SetLike.mem_coe, ← range_componentUnionInclusion]
      exact ⟨_, rfl⟩
    obtain ⟨C, hC, -⟩ := (mem_componentClosedUnion X S _).mp hy
    exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩
    obtain ⟨x, hx⟩ := C.2.1.nonempty
    obtain ⟨y, -⟩ := component_subset_range_componentUnionInclusion X S C hC hx
    exact ⟨y⟩

/-- For a nonempty selection, the dimension of the actual whole union is
the common original dimension. The upper bound uses its actual closed
embedding; a selected original component supplies the lower bound. -/
theorem componentUnionScheme_topologicalKrullDim (d : WithBot ℕ∞)
    (hX : topologicalKrullDim X = d) (hS : S.Nonempty)
    (hdim : ∀ C : ↥(irreducibleComponents X), C ∈ S → topologicalKrullDim C.1 = d) :
    topologicalKrullDim (componentUnionScheme X S) = d := by
  apply le_antisymm
  · exact (IsClosedEmbedding.topologicalKrullDim_le
      (componentUnionInclusion X S).base (componentUnionInclusion X S).isClosedEmbedding).trans
        hX.le
  · obtain ⟨C, hC⟩ := hS
    let e := componentUnionPreimageHomeomorph X S C hC
    have hclosed : IsClosed ((componentUnionInclusion X S).base ⁻¹' C.1) :=
      (isClosed_of_mem_irreducibleComponents C.1 C.2).preimage
        (componentUnionInclusion X S).base.hom.continuous
    calc
      d = topologicalKrullDim C.1 := (hdim C hC).symm
      _ = topologicalKrullDim ((componentUnionInclusion X S).base ⁻¹' C.1) :=
        (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm
      _ ≤ topologicalKrullDim (componentUnionScheme X S) :=
        IsClosedEmbedding.topologicalKrullDim_le
          (Subtype.val : ((componentUnionInclusion X S).base ⁻¹' C.1) →
            componentUnionScheme X S) hclosed.isClosedEmbedding_subtypeVal

/-- The complete dimension-one prerequisite for the original closed
union: the whole scheme and every original component have dimension one.
The nonempty-selection hypothesis prevents an empty-scheme convention
from weakening this conclusion. -/
theorem componentUnionScheme_equidimensional_one
    (hX : topologicalKrullDim X = 1)
    (hcomponents : ∀ C : ↥(irreducibleComponents X), topologicalKrullDim C.1 = 1)
    (hS : S.Nonempty) :
    topologicalKrullDim (componentUnionScheme X S) = 1 ∧
      ∀ D : ↥(irreducibleComponents (componentUnionScheme X S)),
        topologicalKrullDim D.1 = 1 :=
  ⟨componentUnionScheme_topologicalKrullDim X S 1 hX hS (fun C _ => hcomponents C),
    componentUnionComponent_topologicalKrullDim X S 1 (fun C _ => hcomponents C)⟩

end KltDP.Geometry.RationalTreePicard
