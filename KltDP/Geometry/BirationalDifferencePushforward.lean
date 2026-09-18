import KltDP.Geometry.QCartierBirationalPushforward

/-! Original pushforward of a divisor minus the actual target pullback. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

open NormalProjectiveSurface

/-- An exact original integral pushforward identity makes the original
rational divisor minus its target pullback have zero rational pushforward. -/
theorem rationalPushforward_difference_pullback_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (D : S.WeilDivisor) (E : X.WeilDivisor)
    (hE : X.QCartier (rationalizeWeilDivisor X E))
    (hpush : pushforward (S := S) (X := X) π hbir D = E) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    rationalPushforward (S := S) (X := X) π hbir
      (rationalizeWeilDivisor S D -
        QCartierPullback.pullback (X := S) (Y := X) π
          (rationalizeWeilDivisor X E) hE) = 0 := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let F := rationalPushforward (S := S) (X := X) π hbir
  have hD : F (rationalizeWeilDivisor S D) = rationalizeWeilDivisor X E :=
    (rationalPushforward_rationalize (S := S) (X := X) π hbir D).trans
      (congrArg (rationalizeWeilDivisor X) hpush)
  have htarget : F (QCartierPullback.pullback (X := S) (Y := X) π
      (rationalizeWeilDivisor X E) hE) = rationalizeWeilDivisor X E :=
    QCartierPullback.pushforward_pullback (S := S) (X := X) π hbir
      (rationalizeWeilDivisor X E) hE
  exact (F.map_sub _ _).trans
    ((congrArg₂ (fun A B : X.RationalWeilDivisor => A - B) hD htarget).trans
      (sub_self (rationalizeWeilDivisor X E)))

end KltDP.Geometry.BirationalWeilPushforward

#check @KltDP.Geometry.BirationalWeilPushforward.rationalPushforward_difference_pullback_eq_zero
#print axioms KltDP.Geometry.BirationalWeilPushforward.rationalPushforward_difference_pullback_eq_zero
