import KltDP.Geometry.BirationalRationalWeilPushforward

/-!
A proper birational map preserves each surviving coefficient at the unique
original source prime over the original target prime. The prime is the
already constructed closure of the actual lifted generic point. Coefficient
bounds therefore descend through the original rational Weil pushforward.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

/-- A strict common lower coefficient bound descends along the actual
proper birational rational Weil pushforward. -/
theorem coefficient_lower_bound_pushforward
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (D : S.RationalWeilDivisor) (b : ℚ)
    (hD : ∀ C : S.PrimeCurve, b < D C) (C : X.PrimeCurve) :
    b < rationalPushforward (S := S) (X := X) π hbir D C := by
  rw [rationalPushforward_apply]
  exact hD (BirationalPrimeCorrespondence.abovePrimeCurve π hbir C)

/-- Transport a coefficient bound using an equality of the original actual
divisors. The equality is ordinary divisor data, not a canonical comparison. -/
theorem coefficient_lower_bound_of_pushforward_eq
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (D : S.RationalWeilDivisor) (E : X.RationalWeilDivisor) (b : ℚ)
    (hDE : rationalPushforward (S := S) (X := X) π hbir D = E)
    (hD : ∀ C : S.PrimeCurve, b < D C) (C : X.PrimeCurve) : b < E C :=
  (congrArg (fun F : X.RationalWeilDivisor => F C) hDE) ▸
    coefficient_lower_bound_pushforward π hbir D b hD C

/-- The strict discrepancy bound descends through an actual original
pushforward equality; no uniqueness or canonical identity is assumed. -/
theorem coefficient_gt_neg_one_of_pushforward_eq
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (D : S.RationalWeilDivisor) (E : X.RationalWeilDivisor)
    (hDE : rationalPushforward (S := S) (X := X) π hbir D = E)
    (hD : ∀ C : S.PrimeCurve, (-1 : ℚ) < D C) :
    ∀ C : X.PrimeCurve, (-1 : ℚ) < E C :=
  coefficient_lower_bound_of_pushforward_eq π hbir D E (-1) hDE hD

end KltDP.Geometry.BirationalWeilPushforward

#check @KltDP.Geometry.BirationalWeilPushforward.coefficient_gt_neg_one_of_pushforward_eq
#print axioms KltDP.Geometry.BirationalWeilPushforward.coefficient_gt_neg_one_of_pushforward_eq
