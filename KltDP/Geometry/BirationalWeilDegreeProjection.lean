import KltDP.Geometry.BirationalRationalPicardPullback
import KltDP.Geometry.BirationalRationalWeilSupport
import KltDP.Geometry.WeilRestrictionDegree

/-!
# Projection of the original finite Weil restriction degree

The original birational prime correspondence preserves restriction degree
on each noncontracted prime. Contracted primes contribute zero on both
sides. Finite Weil additivity gives the projection formula for every
actual signed Weil divisor and every original target Picard class.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalWeilDegreeProjection

open BirationalPrimeCorrespondence BirationalWeilPushforward

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π)

include hπ hbir

/-- The original finite Weil sum commutes with actual pullback degree and
the original degree-one birational Weil pushforward. -/
theorem picardWeilRestrictionDegree_pushforward
    (p : X.toScheme.Pic) (Z : S.WeilDivisor) :
    S.picardWeilRestrictionDegree (schemePicardPullbackHom π p) Z =
      X.picardWeilRestrictionDegree p (pushforward π hbir Z) := by
  classical
  induction Z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add Z W hZ hW => simp only [map_add, hZ, hW]
  | single C a =>
    by_cases hC : IsExceptionalCurve π C
    · obtain ⟨t, ht, htk⟩ := hC.exists_fieldPoint_factor π hπ C
      rw [S.picardWeilRestrictionDegree_single,
        pushforward_single_contracted π hbir C a t ht htk, map_zero,
        BirationalNumericalPullback.picard_degree_exceptional π hπ C hC p, mul_zero]
    · obtain ⟨E, rfl⟩ := exists_abovePrimeCurve_of_not_exceptional π hbir C hC
      rw [pushforward_single_above, S.picardWeilRestrictionDegree_single,
        X.picardWeilRestrictionDegree_single,
        BirationalProjectionDegree.picardRestrictionDegree_pullback π hπ hbir E p]

end KltDP.Geometry.BirationalWeilDegreeProjection

#check @KltDP.Geometry.BirationalWeilDegreeProjection.picardWeilRestrictionDegree_pushforward
#print axioms KltDP.Geometry.BirationalWeilDegreeProjection.picardWeilRestrictionDegree_pushforward
