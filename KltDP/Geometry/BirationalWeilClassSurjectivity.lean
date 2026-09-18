import KltDP.Geometry.BirationalWeilClassPushforward

/-!
The actual injective correspondence sending a target prime to its unique
source prime gives an explicit lift of original finite Weil sums by the
pinned Finsupp.embDomain map. This lift is a right inverse to original
pushforward. Taking actual quotient representatives then proves surjectivity
of the existing Weil-class pushforward. No class-group splitting or rank
formula is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalWeilClassSurjectivity

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- Lift every original target divisor to its unique source primes,
retaining each original integer coefficient and finite support. -/
def divisorLift : X.WeilDivisor →+ S.WeilDivisor :=
  Finsupp.embDomain.addMonoidHom
    ⟨BirationalPrimeCorrespondence.abovePrimeCurve π hbir,
      BirationalPrimeCorrespondence.abovePrimeCurve_injective π hbir⟩

/-- The explicit lift preserves the original coefficient above each prime. -/
@[simp] theorem divisorLift_apply_above (D : X.WeilDivisor) (C : X.PrimeCurve) :
    divisorLift π hbir D (BirationalPrimeCorrespondence.abovePrimeCurve π hbir C) = D C :=
  Finsupp.embDomain_apply _ _ _

/-- The existing original Weil pushforward recovers every lifted divisor. -/
@[simp] theorem pushforward_divisorLift (D : X.WeilDivisor) :
    BirationalWeilPushforward.pushforward π hbir (divisorLift π hbir D) = D := by
  apply Finsupp.ext
  intro C
  rw [BirationalWeilPushforward.pushforward_apply, divisorLift_apply_above]

/-- Surjectivity on original finite Weil sums has the explicit prime lift. -/
theorem divisor_pushforward_surjective :
    Function.Surjective (BirationalWeilPushforward.pushforward π hbir) :=
  fun D => ⟨divisorLift π hbir D, pushforward_divisorLift π hbir D⟩

/-- Every original target Weil class is the pushforward of the class of
an explicit lifted divisor representative. -/
theorem pushforward_surjective :
    Function.Surjective (BirationalWeilClassPushforward.pushforward π hbir) := by
  intro c
  obtain ⟨D, rfl⟩ := X.weilClassMap_surjective c
  refine ⟨S.weilClassMap (divisorLift π hbir D), ?_⟩
  rw [BirationalWeilClassPushforward.pushforward_weilClassMap, pushforward_divisorLift]

end KltDP.Geometry.BirationalWeilClassSurjectivity
