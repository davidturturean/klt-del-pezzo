import KltDP.Geometry.RationalTreePicardComponentPartition
import KltDP.Geometry.SchematicImageDenseOpen
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The actual schematic closure of a component-union complement

The open complement of a selection of the original irreducible components
has the complementary component union as its closure. Generic points of
the original omitted components prove the density assertion.

When the original scheme is reduced, the kernel of this actual open
inclusion is the vanishing ideal of the complementary component union.
The resulting isomorphism of closed schemes preserves their original maps
to the ambient scheme. This is an ordinary object identification needed
for a future application of the intrinsic nodal cut-intersection lemma;
no nodal hypothesis or intersection-reducedness conclusion is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u}) [NoetherianSpace X]

/-- The literal open complement of the original selected component union. -/
def componentUnionComplementOpen (S : Set ↥(irreducibleComponents X)) : X.Opens :=
  (componentClosedUnion X S).compl

/-- The open complement inherits the original Noetherian topology. -/
instance componentUnionComplementOpen_noetherianSpace (S : Set ↥(irreducibleComponents X)) :
    NoetherianSpace (componentUnionComplementOpen X S).toScheme :=
  (componentUnionComplementOpen X S).ι.isOpenEmbedding.isInducing.noetherianSpace

/-- Hence its actual inclusion is quasi-compact, so its kernel ideal is well behaved. -/
instance componentUnionComplementOpen_ι_quasiCompact (S : Set ↥(irreducibleComponents X)) :
    QuasiCompact (componentUnionComplementOpen X S).ι :=
  quasiCompact_of_noetherianSpace_source _

/-- This is the complement of the range of the actual closed immersion. -/
theorem coe_componentUnionComplementOpen (S : Set ↥(irreducibleComponents X)) :
    (componentUnionComplementOpen X S : Set X) =
      (Set.range (componentUnionInclusion X S).base)ᶜ := by
  rw [range_componentUnionInclusion]
  rfl

/-- An original component's generic point belongs to the selected union
exactly when that same component is selected. -/
theorem genericPoint_mem_componentClosedUnion
    (S : Set ↥(irreducibleComponents X)) (C : ↥(irreducibleComponents X)) :
    C.2.1.genericPoint ∈ componentClosedUnion X S ↔ C ∈ S := by
  have hgeneric := C.2.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents C.1 C.2)
  constructor
  · intro hx
    obtain ⟨D, hD, hxD⟩ := (mem_componentClosedUnion X S _).mp hx
    have hCD : C.1 ⊆ D.1 :=
      (hgeneric.mem_closed_set_iff
        (isClosed_of_mem_irreducibleComponents D.1 D.2)).mp hxD
    have h : C = D := Subtype.ext (hCD.antisymm (C.2.2 D.2.1 hCD))
    exact h.symm ▸ hD
  · intro hC
    exact (mem_componentClosedUnion X S _).mpr ⟨C, hC, hgeneric.mem⟩

/-- The closure is proved from the original generic points and component
coverage, with no density or compatibility assumption. -/
theorem closure_componentUnionComplementOpen (S : Set ↥(irreducibleComponents X)) :
    closure (componentUnionComplementOpen X S : Set X) =
      (componentClosedUnion X Sᶜ : Set X) := by
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ (componentClosedUnion X Sᶜ).isClosed
    intro x hx
    change x ∉ componentClosedUnion X S at hx
    have hcover : x ∈ (componentClosedUnion X S : Set X) ∪
        componentClosedUnion X Sᶜ := by
      rw [componentClosedUnion_union_compl]
      exact Set.mem_univ x
    exact hcover.resolve_left hx
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := (mem_componentClosedUnion X Sᶜ x).mp hx
    have hgeneric : C.2.1.genericPoint ∈ componentUnionComplementOpen X S := by
      change C.2.1.genericPoint ∉ componentClosedUnion X S
      exact fun h => hC ((genericPoint_mem_componentClosedUnion X S C).mp h)
    have hclosure : C.1 ⊆ closure (componentUnionComplementOpen X S : Set X) := by
      rw [← C.2.1.closure_genericPoint
        (isClosed_of_mem_irreducibleComponents C.1 C.2)]
      exact closure_mono (Set.singleton_subset_iff.mpr hgeneric)
    exact hclosure hxC

/-- The kernel support is the actual complementary component union. -/
theorem componentUnionComplementOpen_ker_support
    (S : Set ↥(irreducibleComponents X)) :
    (componentUnionComplementOpen X S).ι.ker.support = componentClosedUnion X Sᶜ := by
  apply Closeds.ext
  rw [Scheme.Hom.support_ker, Scheme.Opens.range_ι, closure_componentUnionComplementOpen]

/-- Reducedness identifies the actual schematic closure ideal with the
existing vanishing ideal of the complementary original components. -/
theorem componentUnionComplementOpen_ker [AlgebraicGeometry.IsReduced X]
    (S : Set ↥(irreducibleComponents X)) :
    (componentUnionComplementOpen X S).ι.ker = componentUnionIdeal X Sᶜ := by
  letI : AlgebraicGeometry.IsReduced (componentUnionComplementOpen X S).toScheme :=
    isReduced_of_isOpenImmersion (componentUnionComplementOpen X S).ι
  calc
    (componentUnionComplementOpen X S).ι.ker =
        (componentUnionComplementOpen X S).ι.ker.radical :=
      (SchematicImageDenseOpen.ker_radical (componentUnionComplementOpen X S).ι).symm
    _ = Scheme.IdealSheafData.vanishingIdeal
        (componentUnionComplementOpen X S).ι.ker.support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = componentUnionIdeal X Sᶜ := by
      rw [componentUnionComplementOpen_ker_support]
      rfl

private theorem eqToIso_glueData_hom_gluedTo {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h)).hom ≫
      J.gluedTo = I.gluedTo := by
  cases h
  simp

/-- The original complement's kernel-closure scheme is isomorphic to the
existing complementary component union, by the proved ideal identity. -/
def componentComplementClosureIso [AlgebraicGeometry.IsReduced X]
    (S : Set ↥(irreducibleComponents X)) :
    (componentUnionComplementOpen X S).ι.ker.glueData.glued ≅
      componentUnionScheme X Sᶜ :=
  eqToIso (congrArg (fun I : X.IdealSheafData => I.glueData.glued)
    (componentUnionComplementOpen_ker X S))

/-- The closure identification commutes with the original inclusions. -/
@[reassoc]
theorem componentComplementClosureIso_hom_over [AlgebraicGeometry.IsReduced X]
    (S : Set ↥(irreducibleComponents X)) :
    (componentComplementClosureIso X S).hom ≫ componentUnionInclusion X Sᶜ =
      (componentUnionComplementOpen X S).ι.ker.gluedTo :=
  eqToIso_glueData_hom_gluedTo X (componentUnionComplementOpen_ker X S)

end KltDP.Geometry.RationalTreePicard
