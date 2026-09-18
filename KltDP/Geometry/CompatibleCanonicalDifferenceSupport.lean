import KltDP.Geometry.BirationalRationalWeilSupport
import KltDP.Geometry.QCartierBirationalPushforward

/-!
# The original compatible canonical difference is actually exceptional

The exact source-to-target Weil pushforward and the proved original
Q-Cartier push-pull identity kill the literal difference. Its support
therefore consists of original contracted primes, by the actual prime
correspondence. No canonical discrepancy equation is supplied.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.MinimalResolutionDiscrepancy

open NormalProjectiveSurface BirationalWeilPushforward

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- Exact compatibility forces zero original pushforward of the literal difference. -/
theorem rationalPushforward_difference_eq_zero
    (KS : CartierDivisor S.toScheme) (KX : X.WeilDivisor)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hpush : pushforward π hbir (S.cartierToWeilHom KS) = KX) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    rationalPushforward π hbir
      (S.rationalCartierToWeilHom KS -
        QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) = 0 := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  change rationalPushforward π hbir
    (rationalizeWeilDivisor S (S.cartierToWeilHom KS) -
      QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK) = 0
  rw [map_sub, rationalPushforward_rationalize, hpush,
    QCartierPullback.pushforward_pullback π hbir, sub_self]

/-- The actual finite support of the original compatible difference consists
only of primes contracted by the original morphism. -/
theorem difference_support_subset_exceptional
    (KS : CartierDivisor S.toScheme) (KX : X.WeilDivisor)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hpush : pushforward π hbir (S.cartierToWeilHom KS) = KX) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    (((S.rationalCartierToWeilHom KS -
      QCartierPullback.pullback π (rationalizeWeilDivisor X KX) hK).support) :
        Set S.PrimeCurve) ⊆ {C | IsExceptionalCurve π C} := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  exact support_subset_exceptional_of_rationalPushforward_eq_zero π hbir _
    (rationalPushforward_difference_eq_zero π hbir KS KX hK hpush)

end KltDP.Geometry.MinimalResolutionDiscrepancy

#check @KltDP.Geometry.MinimalResolutionDiscrepancy.difference_support_subset_exceptional
#print axioms KltDP.Geometry.MinimalResolutionDiscrepancy.difference_support_subset_exceptional
