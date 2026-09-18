import KltDP.Geometry.ActualExceptionalNegativeDefinite
import KltDP.Geometry.ProperBirationalConnectedFibers

/-!
# The original exceptional curves fit below the source Picard rank

An actual ample divisor on the target supplies the positive direction on the
source. All original exceptional primes are orthogonal to its pullback, so
the proved null-curve independence theorem bounds their total number by the
source Picard rank minus one. For an actual resolution the graph-component
surjection also bounds the number of distinct singular points.

These are inequalities, not the still-missing general birational rank equality.
The selected Hodge and numerical-finiteness literature dependencies are retained.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- All actual exceptional primes, together with a produced positive direction,
fit in the original numerical Picard space of the regular source. -/
theorem exceptionalCurves_card_add_one_le_picardRank
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hbir : IsBirationalScheme π)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x) :
    Nat.card (ActualExceptionalIncidence.Vertices π) + 1 ≤ S.picardRank := by
  classical
  letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
    (exceptionalCurves_finite_of_proper_birational π hbir).fintype
  obtain ⟨H, hH, hnull⟩ :=
    ActualExceptionalNegativeDefinite.exists_positive_square_orthogonal_divisor
      π hπ hbir hregular
  simpa only [Nat.card_eq_fintype_card] using
    NullCurveIndependenceRank.card_add_one_le_picardRank S hregular H hH
      (fun C : ActualExceptionalIncidence.Vertices π => C.val)
      Subtype.val_injective (fun C => hnull C.val C.property)

/-- An actual resolution bounds the number of distinct singular points by
the original source Picard rank minus one, without a connectedness premise. -/
theorem IsResolution.singularPoints_card_add_one_le_picardRank
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    {π : S.toScheme ⟶ X.toScheme} (hres : IsResolution S X π) :
    X.singularPoints.card + 1 ≤ S.picardRank := by
  letI : IsProper π := hres.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hres.birational
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  have hcount :=
    (ProperBirationalConnectedFibers.singularPoints_card_le_graph_components π hres).2
  have hcomponents : Nat.card (ActualExceptionalIncidence.graph π).ConnectedComponent ≤
      Nat.card (ActualExceptionalIncidence.Vertices π) :=
    Nat.card_le_card_of_surjective (ActualExceptionalIncidence.graph π).connectedComponentMk
      (fun c => Quot.exists_rep c)
  exact (Nat.add_le_add_right (hcount.trans hcomponents) 1).trans
    (exceptionalCurves_card_add_one_le_picardRank π hres.over_base hbir hres.regular)

end KltDP.Geometry

#print axioms KltDP.Geometry.exceptionalCurves_card_add_one_le_picardRank
#print axioms KltDP.Geometry.IsResolution.singularPoints_card_add_one_le_picardRank
