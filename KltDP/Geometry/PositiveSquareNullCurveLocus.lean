import KltDP.Geometry.NullCurveIndependenceRank

/-!
# Finiteness and rank of degree-zero curves for the original line bundle

The actual Cartier representative of an arbitrary invertible sheaf preserves
its square and all prime-curve degrees. The proved null-curve independence
and rank theorem therefore apply to the original line bundle, and its
degree-zero curve union is already closed.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.PositiveSquareNullCurveLocus

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- An original invertible sheaf of positive square has finitely many
degree-zero curves, whose total number is at most rho minus one. -/
theorem finite_and_card_bound (L : InvertibleSheaf X.toScheme)
    (hpositive : 0 < X.selfIntersection hregular L) :
    {C : X.PrimeCurve | C.restrictionDegree L = 0}.Finite ∧
      Nat.card {C : X.PrimeCurve // C.restrictionDegree L = 0} + 1 ≤ X.picardRank := by
  let A := X.picardRepresentative L.toPic
  have hclass : cartierPicardClass X.toScheme A = L.toPic :=
    X.cartierPicardClass_picardRepresentative L.toPic
  have hA : 0 < X.intersectionPairing hregular A A := by
    rw [← X.picardPairing_class hregular, hclass]
    exact hpositive
  have hcurve (C : X.PrimeCurve) : C.intersectionNumber A = C.restrictionDegree L := by
    rw [C.intersectionNumber_eq_picardRestrictionDegree, hclass,
      C.picardRestrictionDegree_toPic]
  constructor
  · simpa only [hcurve] using
      NullCurveIndependenceRank.finite_null_curves X hregular A hA
  · simpa only [hcurve] using
      NullCurveIndependenceRank.null_curves_card_add_one_le_picardRank X hregular A hA

/-- The actual union of degree-zero prime curves is closed for an
original line bundle of positive square. -/
theorem isClosed_union (L : InvertibleSheaf X.toScheme)
    (hpositive : 0 < X.selfIntersection hregular L) :
    IsClosed (⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0},
      (C : Set X.toScheme)) :=
  (finite_and_card_bound X hregular L hpositive).1.isClosed_biUnion (fun C _ => C.isClosed)

/-- The closure in the existing surface null-locus expression adds
no points to the original degree-zero curve union. -/
theorem closure_union (L : InvertibleSheaf X.toScheme)
    (hpositive : 0 < X.selfIntersection hregular L) :
    closure (⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0},
      (C : Set X.toScheme)) =
      ⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme) :=
  (isClosed_union X hregular L hpositive).closure_eq

end KltDP.Geometry.PositiveSquareNullCurveLocus
