import KltDP.Geometry.ExceptionalForestBlockCurves
import KltDP.Geometry.TransversalClosedPrimeUnion
import KltDP.Geometry.KltMinimalResolutionCrossing
import KltDP.Geometry.KltResolutionExceptionalProjectiveLine
import KltDP.Geometry.ActualExceptionalNoTriple

/-!
# Original klt exceptional blocks have their actual transverse crossing germs

The source regularity, exceptional projective-line identifications, original
incidence forest and original maximal-ideal sums are all derived from the
actual minimal resolution and the target's klt property. The reduced block
and its original curve maps therefore form a transversal configuration.
No incidence dictionary, local equation or product-kernel premise is supplied.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ExceptionalForestClosedBlocks

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
  (b : (ActualExceptionalIncidence.graph π).ConnectedComponent)

/-- The full crossing configuration of the original reduced exceptional block. -/
theorem block_transversalConfiguration (hmin : IsMinimalResolution S X π) (hklt : IsKlt X) :
    RationalTreePicard.TransversalConfiguration (blockInclusion π hbir b) := by
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  letI : Fintype b.supp := Fintype.ofFinite _
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  have hrational := hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt hklt
  have hforest := (hmin.exceptional_forest_and_singular_count_of_klt hklt hrational).2.2.1
  have hinj : Function.Injective (fun E : b.supp => E.val.val) := by
    intro E F h
    exact Subtype.ext (Subtype.ext h)
  apply TransversalClosedPrimeUnion.transversalConfiguration_of_original_primes
    S hmin.regular (fun E : b.supp => E.val.val) (blockInclusion π hbir b)
    (blockCurve π hbir b) (blockCurve_inclusion π hbir b) hinj
  · exact range_blockInclusion π hbir b
  · intro E F G x hxE hxF hxG
    rcases KltDP.Topology.no_three_of_incidence_isAcyclic
        (fun C : ActualExceptionalIncidence.Vertices π => (C.val : Set S.toScheme))
        hforest E.val F.val G.val x hxE hxF hxG with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · intro E F hEF x hxE hxF U hxU
    have hCD : E.val.val ≠ F.val.val := fun h => hEF (hinj h)
    change x ∈ (E.val.val : Set S.toScheme) at hxE
    rw [← E.val.val.range_inclusion] at hxE
    obtain ⟨y, rfl⟩ := hxE
    exact KltMinimalResolutionCrossing.vanishingIdeal_sup_eq_maximalIdeal hmin hklt hrational
      E.val.val F.val.val E.val.property F.val.property hCD y hxF U hxU

end KltDP.Geometry.ExceptionalForestClosedBlocks

#check @KltDP.Geometry.ExceptionalForestClosedBlocks.block_transversalConfiguration
#print axioms KltDP.Geometry.ExceptionalForestClosedBlocks.block_transversalConfiguration
