import KltDP.Geometry.UnbranchedExceptionalBlockBranchDisjoint
import KltDP.Geometry.KltExceptionalBlockGeometry

/-!
# All actual unbranched reduced components are all original retained primes

The sigma index ranges over every original unbranched graph block and
all its actual irreducible components. The proved component dictionary
identifies this index with the original exceptional primes outside N,
retaining actual prime curves, injectivity, and the exact r minus n count.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence ExceptionalForestClosedBlocks RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    [IsProper π] (hbir : IsBirationalScheme π)

/-- Every actual reduced component of every unbranched original block. -/
abbrev Components := Σ b : Blocks π N, ↥(irreducibleComponents (blockScheme π hbir b.val))

/-- The actual component dictionary on all retained blocks at once. -/
def componentVertexEquiv : Components π N hbir ≃ BlockVertices π N :=
  Equiv.sigmaCongrRight (fun b => (blockComponentEquiv π hbir b.val).symm)

/-- The original exceptional vertex represented by an actual block component. -/
def originalVertex (i : Components π N hbir) : Vertices π :=
  vertex π N (componentVertexEquiv π N hbir i)

/-- The original component prime family is distinct over all unbranched blocks. -/
theorem originalVertex_injective : Function.Injective (originalVertex π N hbir) :=
  (vertex_injective π N).comp (componentVertexEquiv π N hbir).injective

/-- The component index has exactly r minus n members, derived from the original block dictionary. -/
theorem card_components (hiso : IsolatedSelection π N)
    (hN : ∀ A ∈ N, IsExceptionalCurve π A) :
    Nat.card (Components π N hbir) = Nat.card (Vertices π) - N.card :=
  (Nat.card_congr (componentVertexEquiv π N hbir)).trans (card_blockVertices π N hiso hbir hN)

variable (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)

/-- The actual base prime constructed from each original reduced block component. -/
def baseCurve (i : Components π N hbir) : S.PrimeCurve :=
  RationalComponentPrimeCurves.curve S (blockInclusion π hbir i.1.val)
    (blockComponentProjectiveLineIso π hbir i.1.val hmin hklt) i.2

/-- The constructed component prime is precisely its original exceptional prime. -/
theorem baseCurve_eq_original (i : Components π N hbir) :
    baseCurve π N hbir hmin hklt i = (originalVertex π N hbir i).val :=
  block_componentPrime_eq_original π hbir i.1.val
    (blockComponentProjectiveLineIso π hbir i.1.val hmin hklt) i.2

/-- The full actual base prime family remains injective over every retained block. -/
theorem baseCurve_injective : Function.Injective (baseCurve π N hbir hmin hklt) := by
  intro i j h
  apply originalVertex_injective π N hbir
  apply Subtype.ext
  simpa only [baseCurve_eq_original π N hbir hmin hklt] using h

/-- All original base components are contracted by the original resolution morphism. -/
theorem baseCurve_contracted (i : Components π N hbir) :
    IsExceptionalCurve π (baseCurve π N hbir hmin hklt i) := by
  rw [baseCurve_eq_original]
  exact (originalVertex π N hbir i).property

/-- Distinct original blocks have disjoint actual original component primes. -/
theorem baseCurve_disjoint_of_block_ne (i j : Components π N hbir) (hij : i.1 ≠ j.1) :
    Disjoint (baseCurve π N hbir hmin hklt i : Set S.toScheme)
      (baseCurve π N hbir hmin hklt j : Set S.toScheme) := by
  rw [baseCurve_eq_original, baseCurve_eq_original]
  apply (blockSupport_disjoint π (fun h => hij (Subtype.ext h))).mono
  · exact prime_subset_blockSupport π i.1.val ((blockComponentEquiv π hbir i.1.val).symm i.2)
  · exact prime_subset_blockSupport π j.1.val ((blockComponentEquiv π hbir j.1.val).symm j.2)

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.card_components
#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.baseCurve_injective
#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.baseCurve_contracted
