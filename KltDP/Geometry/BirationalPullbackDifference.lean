import KltDP.Geometry.BirationalCoefficientBounds
import KltDP.Geometry.QCartierBirationalPushforward
import KltDP.Geometry.QCartierPullbackFunctorial

/-!
Original pullback composition and birational push-pull give the actual
pushforward identity for a divisor minus a composite pullback. The source
divisor is arbitrary: the conclusion retains its literal pushforward and
assumes no independent canonical or crepant compatibility.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

/-- Pushforward along the actual proper birational first map cancels that
factor in the original composite Q-Cartier pullback. -/
theorem rationalPushforward_composite_pullback
    {k : Type u} [Field k] [IsAlgClosed k] {T X Y : NormalProjectiveSurface k}
    (q : T.toScheme ⟶ X.toScheme) (f : X.toScheme ⟶ Y.toScheme)
    [IsProper q] (hbir : IsBirationalScheme q) [GenericPointPreserving f]
    (B : Y.RationalWeilDivisor) (hB : Y.QCartier B) :
    letI : GenericPointPreserving q := ⟨hbir.map_genericPoint⟩
    rationalPushforward (S := T) (X := X) q hbir
        (QCartierPullback.pullback (X := T) (Y := Y) (q ≫ f) B hB) =
      QCartierPullback.pullback (X := X) (Y := Y) f B hB := by
  letI : GenericPointPreserving q := ⟨hbir.map_genericPoint⟩
  exact (congrArg (rationalPushforward (S := T) (X := X) q hbir)
      (QCartierPullback.pullback_comp (X := T) (Y := X) (Z := Y) q f B hB)).trans
    (QCartierPullback.pushforward_pullback (S := T) (X := X) q hbir
      (QCartierPullback.pullback (X := X) (Y := Y) f B hB)
      (QCartierPullback.pullback_qCartier (X := X) (Y := Y) f B hB))

/-- Equality of the original rational divisors, with the first term kept
as its actual pushforward and no canonical compatibility assumed. -/
theorem rationalPushforward_difference_composite_pullback
    {k : Type u} [Field k] [IsAlgClosed k] {T X Y : NormalProjectiveSurface k}
    (q : T.toScheme ⟶ X.toScheme) (f : X.toScheme ⟶ Y.toScheme)
    [IsProper q] (hbir : IsBirationalScheme q) [GenericPointPreserving f]
    (D : T.RationalWeilDivisor) (B : Y.RationalWeilDivisor) (hB : Y.QCartier B) :
    letI : GenericPointPreserving q := ⟨hbir.map_genericPoint⟩
    rationalPushforward (S := T) (X := X) q hbir
        (D - QCartierPullback.pullback (X := T) (Y := Y) (q ≫ f) B hB) =
      rationalPushforward (S := T) (X := X) q hbir D -
        QCartierPullback.pullback (X := X) (Y := Y) f B hB := by
  letI : GenericPointPreserving q := ⟨hbir.map_genericPoint⟩
  exact ((rationalPushforward (S := T) (X := X) q hbir).map_sub _ _).trans
    (congrArg (fun E : X.RationalWeilDivisor =>
      rationalPushforward (S := T) (X := X) q hbir D - E)
      (rationalPushforward_composite_pullback q f hbir B hB))

/-- The strict coefficient bound descends for this actual original divisor
difference, using the derived pushforward identity rather than an assumed one. -/
theorem coefficient_gt_neg_one_difference_of_composite
    {k : Type u} [Field k] [IsAlgClosed k] {T X Y : NormalProjectiveSurface k}
    (q : T.toScheme ⟶ X.toScheme) (f : X.toScheme ⟶ Y.toScheme)
    [IsProper q] (hbir : IsBirationalScheme q) [GenericPointPreserving f]
    (D : T.RationalWeilDivisor) (B : Y.RationalWeilDivisor) (hB : Y.QCartier B) :
    letI : GenericPointPreserving q := ⟨hbir.map_genericPoint⟩
    (∀ C : T.PrimeCurve, (-1 : ℚ) <
      (D - QCartierPullback.pullback (X := T) (Y := Y) (q ≫ f) B hB) C) →
    ∀ C : X.PrimeCurve, (-1 : ℚ) <
      (rationalPushforward (S := T) (X := X) q hbir D -
        QCartierPullback.pullback (X := X) (Y := Y) f B hB) C := by
  letI : GenericPointPreserving q := ⟨hbir.map_genericPoint⟩
  intro hD
  exact coefficient_gt_neg_one_of_pushforward_eq q hbir
    (D - QCartierPullback.pullback (X := T) (Y := Y) (q ≫ f) B hB)
    (rationalPushforward (S := T) (X := X) q hbir D -
      QCartierPullback.pullback (X := X) (Y := Y) f B hB)
    (rationalPushforward_difference_composite_pullback q f hbir D B hB) hD

end KltDP.Geometry.BirationalWeilPushforward

#check @KltDP.Geometry.BirationalWeilPushforward.rationalPushforward_difference_composite_pullback
#check @KltDP.Geometry.BirationalWeilPushforward.coefficient_gt_neg_one_difference_of_composite
#print axioms KltDP.Geometry.BirationalWeilPushforward.rationalPushforward_difference_composite_pullback
#print axioms KltDP.Geometry.BirationalWeilPushforward.coefficient_gt_neg_one_difference_of_composite
