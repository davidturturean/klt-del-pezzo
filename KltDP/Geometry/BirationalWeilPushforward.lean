import KltDP.Geometry.BirationalPrimeCorrespondence
import KltDP.Geometry.PrimeCurvePointFiberFactorization

/-!
The original proper birational morphism determines the unique prime above
each target prime, with an isomorphic original generic stalk. Its degree-one
Weil pushforward is the existing finite-sum comap along this proved injective
correspondence. Contracted original primes have zero pushforward.
Principal-divisor and canonical compatibility are separate next proofs.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalWeilPushforward

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- Pushforward on the actual finite Weil sums, using the original unique
prime correspondence. The generic residue extension has degree one because
the corresponding original stalk map is an isomorphism. -/
def pushforward : S.WeilDivisor →+ X.WeilDivisor :=
  Finsupp.comapDomain.addMonoidHom (abovePrimeCurve_injective π hbir)

@[simp] theorem pushforward_apply (D : S.WeilDivisor) (C : X.PrimeCurve) :
    pushforward π hbir D C = D (abovePrimeCurve π hbir C) := rfl

/-- The unique prime above an original target prime pushes to that prime
with its original integer coefficient. -/
theorem pushforward_single_above (C : X.PrimeCurve) (z : ℤ) :
    pushforward π hbir (Finsupp.single (abovePrimeCurve π hbir C) z) =
      Finsupp.single C z := by
  exact Finsupp.comapDomain_single (abovePrimeCurve π hbir) C z _

include hbir in
/-- A prime contracted to an original field point cannot be the prime
above any target curve: the latter generic point is nonclosed. -/
theorem contracted_ne_above (B : S.PrimeCurve)
    (p : Spec (CommRingCat.of k) ⟶ X.toScheme)
    (hB : B.inclusion ≫ π = B.toSpec ≫ p) (hp : p ≫ X.structureMorphism = 𝟙 _)
    (C : X.PrimeCurve) : B ≠ abovePrimeCurve π hbir C := by
  intro h
  have heq : C.genericPoint = fieldMorphismPoint p := by
    calc
      C.genericPoint = π.base (abovePrimeCurve π hbir C).genericPoint :=
        (abovePrimeCurve_map_genericPoint π hbir C).symm
      _ = π.base B.genericPoint := congrArg (fun D : S.PrimeCurve => π.base D.genericPoint) h.symm
      _ = fieldMorphismPoint p :=
        PrimeCurvePointFiberFactorization.base_eq_on_prime_of_factor S B π p hB
          B.genericPoint B.genericPoint_mem
  exact C.not_isClosed_singleton_genericPoint
    (heq.symm ▸ isClosed_point_of_section X.structureMorphism p hp)

/-- Every actually contracted prime is killed by the actual finite-sum
pushforward, including arbitrary signed integer coefficients. -/
theorem pushforward_single_contracted (B : S.PrimeCurve) (z : ℤ)
    (p : Spec (CommRingCat.of k) ⟶ X.toScheme)
    (hB : B.inclusion ≫ π = B.toSpec ≫ p) (hp : p ≫ X.structureMorphism = 𝟙 _) :
    pushforward π hbir (Finsupp.single B z) = 0 := by
  ext C
  change (Finsupp.single B z) (abovePrimeCurve π hbir C) = 0
  exact Finsupp.single_eq_of_ne (contracted_ne_above π hbir B p hB hp C)

end KltDP.Geometry.BirationalWeilPushforward
