import KltDP.Geometry.PositiveSquareNefNullLocus

/-!
# The actual exceptional subvarieties of a nef positive-square line bundle

On the original smooth projective surface, a non-big positive-dimensional
subvariety is exactly a prime curve of degree zero. The full exceptional
subvariety type is therefore equivalent to the actual null-curve type, with
no chosen list or assumed finiteness. Its cardinality is at most rho minus one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PositiveSquareExceptionalSubvarieties

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- The original exceptional-subvariety predicate is exactly the conjunction
of dimension one and original restriction degree zero. -/
theorem isExceptional_iff (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth L)
    (Z : IrreducibleCloseds X.toScheme) :
    Positivity.IsExceptionalSubvariety X.structureMorphism L Z ↔
      topologicalKrullDim (Z : Set X.toScheme) = 1 ∧
        Positivity.subvarietyDegree X.structureMorphism L Z = 0 := by
  constructor
  · intro hZ
    rcases X.irreducibleClosed_dim_eq_one_or_eq_univ Z hZ.1 with hdim | hwhole
    · exact ⟨hdim, (PrimeCurveBigness.isExceptional_iff_degree_zero X L hnef
        (⟨Z, hdim⟩ : X.PrimeCurve)).mp hZ⟩
    · exact (hZ.2 (PositiveSquareNefNullLocus.whole_subvariety_isBig X L
        (NefPositiveSelfIntersectionBig.isBig X L hnef hpositive) Z hwhole)).elim
  · rintro ⟨hdim, hdegree⟩
    exact (PrimeCurveBigness.isExceptional_iff_degree_zero X L hnef
      (⟨Z, hdim⟩ : X.PrimeCurve)).mpr hdegree

/-- Every actual exceptional subvariety is its original prime curve, and
every original null curve is an exceptional subvariety. -/
def exceptionalEquivNullCurves (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth L) :
    {Z : IrreducibleCloseds X.toScheme //
      Positivity.IsExceptionalSubvariety X.structureMorphism L Z} ≃
      {C : X.PrimeCurve // C.restrictionDegree L = 0} where
  toFun Z :=
    ⟨⟨Z.1, ((isExceptional_iff X L hnef hpositive Z.1).mp Z.2).1⟩,
      ((isExceptional_iff X L hnef hpositive Z.1).mp Z.2).2⟩
  invFun C := ⟨C.1.1,
    (PrimeCurveBigness.isExceptional_iff_degree_zero X L hnef C.1).mpr C.2⟩
  left_inv Z := Subtype.ext rfl
  right_inv C := Subtype.ext (Subtype.ext rfl)

/-- The actual exceptional subvarieties form a finite set, and their count
plus one is at most the original surface Picard rank. -/
theorem finite_and_card_bound (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth L) :
    {Z : IrreducibleCloseds X.toScheme |
      Positivity.IsExceptionalSubvariety X.structureMorphism L Z}.Finite ∧
      Nat.card {Z : IrreducibleCloseds X.toScheme //
        Positivity.IsExceptionalSubvariety X.structureMorphism L Z} + 1 ≤ X.picardRank := by
  have hcurves := PositiveSquareNullCurveLocus.finite_and_card_bound X
    X.regularPoints_of_isSmooth L hpositive
  let e := exceptionalEquivNullCurves X L hnef hpositive
  letI : Finite {C : X.PrimeCurve // C.restrictionDegree L = 0} :=
    Set.finite_coe_iff.mpr hcurves.1
  constructor
  · exact Set.finite_coe_iff.mp (Finite.of_equiv _ e.symm)
  · rw [Nat.card_congr e]
    exact hcurves.2

end KltDP.Geometry.PositiveSquareExceptionalSubvarieties
