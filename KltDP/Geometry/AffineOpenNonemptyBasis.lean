import KltDP.Geometry.AffineOpenRefinement
import Mathlib.Topology.Sets.Opens

/-!
# Nonempty affine subopens of an original cover form a basis

This filters only the index used to check a sheaf isomorphism. The
original atlas, glued scheme, and structural morphism remain literal.
Nontriviality of the original section rings follows from an actual stalk.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry.AffineOpenRefinement

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)

/-- The original subordinate affine opens which contain a point. -/
abbrev NonemptyIndex := {i : Index X U // Nonempty (opens X U i)}

instance nonemptyIndex_sectionRing_nontrivial (i : NonemptyIndex X U) :
    Nontrivial Γ(X, opens X U i.val) := by
  letI : Nonempty (opens X U i.val) := i.property
  infer_instance

/-- Filtering out empty original affine charts still gives an actual basis. -/
theorem nonempty_isBasis (hU : (⨆ i, U i) = ⊤) :
    Opens.IsBasis (Set.range (fun i : NonemptyIndex X U => opens X U i.val)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro W x hx
  have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open
      (show x ∈ W ⊓ U i from ⟨hx, hi⟩) (W ⊓ U i).2
  have hsub : V ≤ W ⊓ U i := hVW
  let j : Index X U := ⟨i, ⟨V, hV, hsub.trans inf_le_right⟩⟩
  refine ⟨V, ⟨⟨j, ⟨⟨x, hxV⟩⟩⟩, rfl⟩, hxV, hsub.trans inf_le_left⟩

end KltDP.Geometry.AffineOpenRefinement

#check @KltDP.Geometry.AffineOpenRefinement.nonempty_isBasis
#print axioms KltDP.Geometry.AffineOpenRefinement.nonempty_isBasis
