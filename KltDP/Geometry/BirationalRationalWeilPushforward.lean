import KltDP.Geometry.BirationalWeilPushforward
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Original rational Weil pushforward

Pinned `Finsupp.lcomapDomain` extends the original integral pushforward
along exactly the same injective prime correspondence. The divisor group
is the original finite rational sum of actual prime curves. Its literal
coefficient formula commutes with original coefficient rationalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- Rational linear pushforward on the existing rational Weil divisor groups. -/
def rationalPushforward : S.RationalWeilDivisor →ₗ[ℚ] X.RationalWeilDivisor :=
  Finsupp.lcomapDomain (abovePrimeCurve π hbir) (abovePrimeCurve_injective π hbir)

@[simp]
theorem rationalPushforward_apply (D : S.RationalWeilDivisor) (C : X.PrimeCurve) :
    rationalPushforward π hbir D C = D (abovePrimeCurve π hbir C) := rfl

/-- The rational map extends the original integral pushforward through
the original coefficient inclusion. -/
@[simp]
theorem rationalPushforward_rationalize (D : S.WeilDivisor) :
    rationalPushforward π hbir (NormalProjectiveSurface.rationalizeWeilDivisor S D) =
      NormalProjectiveSurface.rationalizeWeilDivisor X (pushforward π hbir D) := by
  apply Finsupp.ext
  intro C
  rfl

/-- The unique original prime above a target prime keeps its actual rational coefficient. -/
theorem rationalPushforward_single_above (C : X.PrimeCurve) (q : ℚ) :
    rationalPushforward π hbir (Finsupp.single (abovePrimeCurve π hbir C) q) =
      Finsupp.single C q :=
  Finsupp.comapDomain_single (abovePrimeCurve π hbir) C q _

/-- An actually contracted prime is killed, with any rational coefficient. -/
theorem rationalPushforward_single_contracted (B : S.PrimeCurve) (q : ℚ)
    (p : Spec (CommRingCat.of k) ⟶ X.toScheme)
    (hB : B.inclusion ≫ π = B.toSpec ≫ p) (hp : p ≫ X.structureMorphism = 𝟙 _) :
    rationalPushforward π hbir (Finsupp.single B q) = 0 := by
  apply Finsupp.ext
  intro C
  change (Finsupp.single B q) (abovePrimeCurve π hbir C) = 0
  exact Finsupp.single_eq_of_ne (contracted_ne_above π hbir B p hB hp C)

end KltDP.Geometry.BirationalWeilPushforward
