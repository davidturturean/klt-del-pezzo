import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Connected.Clopen

/-!
Connected nontrivial Noetherian spaces have no singleton irreducible
components. The pinned open-part theorem for an irreducible component
makes any singleton component clopen, contradicting connectedness.
Applied to a closed connected subset, this supplies a nontrivial ambient
irreducible closed subset through each of its points.
-/

noncomputable section

open Set TopologicalSpace

namespace KltDP.Topology.ConnectedNoetherianFibers

variable {T : Type*} [TopologicalSpace T] [NoetherianSpace T]

/-- Every actual irreducible component of a connected nontrivial
Noetherian space contains at least two points. -/
theorem irreducibleComponent_nontrivial [ConnectedSpace T] [Nontrivial T]
    {Z : Set T} (hZ : Z ∈ irreducibleComponents T) : Z.Nontrivial := by
  classical
  by_contra hn
  have hsub : Z.Subsingleton := Set.not_nontrivial_iff.mp hn
  obtain ⟨U, hUopen, hUne, hUZ⟩ :=
    NoetherianSpace.exists_open_ne_empty_le_irreducibleComponent Z hZ
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hUne
  have hUZeq : U = Z := by
    apply Set.Subset.antisymm hUZ
    intro z hz
    have hzx : z = x := hsub hz (hUZ hx)
    simpa only [hzx] using hx
  have hclopen : IsClopen Z :=
    ⟨isClosed_of_mem_irreducibleComponents Z hZ, hUZeq ▸ hUopen⟩
  have hfull : Z = Set.univ := hclopen.eq_univ hZ.1.nonempty
  exact hn (hfull.symm ▸ Set.nontrivial_univ)

/-- Every point of a closed connected nontrivial subset lies in a
nontrivial irreducible closed subset of the ambient space contained in it. -/
theorem exists_nontrivial_irreducibleClosed_subset
    (s : Set T) (hs : IsClosed s) (hconnected : IsConnected s)
    (hnt : s.Nontrivial) (x : T) (hx : x ∈ s) :
    ∃ Z : IrreducibleCloseds T,
      x ∈ Z ∧ (Z : Set T).Nontrivial ∧ (Z : Set T) ⊆ s := by
  letI : ConnectedSpace s := isConnected_iff_connectedSpace.mp hconnected
  letI : Nontrivial s := hnt.coe_sort
  let xs : s := ⟨x, hx⟩
  let S : Set s := irreducibleComponent xs
  have hS : S ∈ irreducibleComponents s := irreducibleComponent_mem_irreducibleComponents xs
  let Z : IrreducibleCloseds T :=
    ⟨Subtype.val '' S, hS.1.image Subtype.val continuous_subtype_val.continuousOn,
      hs.isClosedMap_subtype_val S (isClosed_of_mem_irreducibleComponents S hS)⟩
  refine ⟨Z, ?_, (irreducibleComponent_nontrivial hS).image Subtype.val_injective, ?_⟩
  · exact ⟨xs, mem_irreducibleComponent, rfl⟩
  · rintro z ⟨w, hw, rfl⟩
    exact w.property

end KltDP.Topology.ConnectedNoetherianFibers
