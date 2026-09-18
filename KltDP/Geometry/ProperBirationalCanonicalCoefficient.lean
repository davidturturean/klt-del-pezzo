import KltDP.Geometry.ProperBirationalCanonicalRestriction
import KltDP.Geometry.DominantCartierPullbackFunctorial
import KltDP.Geometry.QCartierPullback

/-!
# Original detected-prime coefficients on a normal model's big open

The original codimension-one target point belongs to the single target
isomorphism open. The coefficient of the fixed source divisor equals the
order of its actual constructed Cartier restriction there. Original
Cartier and rational Cartier pullbacks over the original target satisfy
the same formula. No equality of chosen canonical coefficients is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperBirationalCanonicalCoefficient

open ProperBirationalCanonicalOpen ProperBirationalCanonicalRestriction
open OpenImmersionRational DominantCartierPullback

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)
    {V : Scheme.{u}} [IsIntegral V] (q : S.toScheme ⟶ V) [IsProper q]
    (hbir : IsBirationalScheme q) (fV : V ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fV] (hnormal : IsNormalScheme V)

local instance liftOpen {Y Z : Scheme.{u}} (a : Y ⟶ Z) :
    IsOpenImmersion (lift a) := lift_isOpenImmersion a

local instance openGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (e : Y ⟶ Z) [IsOpenImmersion e] : GenericPointPreserving e :=
  ⟨genericPoint_eq_of_isOpenImmersion e⟩

/-- The very same original target divisorial point in its big open. -/
def point (x : CodimensionOnePoint V) : (targetIsomorphismOpen q).toScheme :=
  ⟨x.val, codimensionOne_mem q hbir fV hnormal x⟩

/-- Its DVR is derived from the original normal finite-type target stalk. -/
theorem point_isDiscreteValuationRing (x : CodimensionOnePoint V) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    IsDiscreteValuationRing ((targetIsomorphismOpen q).toScheme.presheaf.stalk
      (point S q hbir fV hnormal x)) := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI := normalFiniteTypePoint_isDiscreteValuationRing fV hnormal x
  exact stalk_isDiscreteValuationRing_of_isOpenImmersion
    (targetIsomorphismOpen q).ι (point S q hbir fV hnormal x) x.val rfl

/-- The original inverse restriction recovers the detected source prime point. -/
theorem lift_point (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hD : q.base D.genericPoint = x.val) :
    (lift q).base (point S q hbir fV hnormal x) = D.genericPoint := by
  have hs : q.base D.genericPoint ∈ targetIsomorphismOpen q := by
    rw [hD]
    exact codimensionOne_mem q hbir fV hnormal x
  have hp : (⟨q.base D.genericPoint, hs⟩ : (targetIsomorphismOpen q).toScheme) =
      point S q hbir fV hnormal x := Subtype.ext hD
  simpa only [hp] using lift_base q D.genericPoint hs

/-- An arbitrary fixed source Cartier divisor has exactly the transported
order at the original target point, equal to its actual Weil coefficient. -/
theorem divisor_order (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hD : q.base D.genericPoint = x.val) (KS : CartierDivisor S.toScheme) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    letI := point_isDiscreteValuationRing S q hbir fV hnormal x
    cartierOrderAt (targetIsomorphismOpen q).toScheme (divisor q hbir KS)
        (point S q hbir fV hnormal x) = S.cartierToWeilHom KS D := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI := point_isDiscreteValuationRing S q hbir fV hnormal x
  letI := D.genericPoint_isDiscreteValuationRing
  exact divisor_orderAt q hbir KS (point S q hbir fV hnormal x)
    D.genericPoint (lift_point S q hbir fV hnormal D x hD)

section OverTarget

variable {X : Scheme.{u}} [IsIntegral X]
    (π : S.toScheme ⟶ X) (v : V ⟶ X)
    [GenericPointPreserving π] [GenericPointPreserving v]
    (hcomm : q ≫ v = π)

include hcomm

/-- The fixed pullback divisor restricts to the pullback along the original
target-open structure map, using the original over-target equation. -/
theorem divisor_pullback (A : CartierDivisor X) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    divisor q hbir (pullbackHom π A) =
      pullbackHom ((targetIsomorphismOpen q).ι ≫ v) A := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  have hmaps := structure_eq q π v hcomm
  have h := congrArg (fun F => F A) (pullbackHom_comp (lift q) π)
  change pullbackHom (lift q ≫ π) A = pullbackHom (lift q) (pullbackHom π A) at h
  simpa only [hmaps] using h.symm

/-- Exact integral pullback coefficients on the original source agree with
the original target-open Cartier orders at the detected divisor. -/
theorem pullback_order (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hD : q.base D.genericPoint = x.val) (A : CartierDivisor X) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    letI := point_isDiscreteValuationRing S q hbir fV hnormal x
    S.cartierToWeilHom (pullbackHom π A) D =
      cartierOrderAt (targetIsomorphismOpen q).toScheme
        (pullbackHom ((targetIsomorphismOpen q).ι ≫ v) A)
        (point S q hbir fV hnormal x) := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI := point_isDiscreteValuationRing S q hbir fV hnormal x
  have h := divisor_order S q hbir fV hnormal D x hD (pullbackHom π A)
  rw [divisor_pullback S q hbir π v hcomm A] at h
  exact h.symm

end OverTarget

section RationalOverTarget

variable [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (π : S.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    [GenericPointPreserving π] [GenericPointPreserving v]
    (hcomm : q ≫ v = π)

include hcomm

/-- Every actual positive Cartier numerator computes the same original
rational pullback coefficient on the target big open. -/
theorem rational_pullback_order (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hD : q.base D.genericPoint = x.val)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • B) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    letI := point_isDiscreteValuationRing S q hbir fV hnormal x
    QCartierPullback.pullback π B hB D =
      (n : ℚ)⁻¹ * (cartierOrderAt (targetIsomorphismOpen q).toScheme
        (pullbackHom ((targetIsomorphismOpen q).ι ≫ v) A)
        (point S q hbir fV hnormal x) : ℚ) := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI := point_isDiscreteValuationRing S q hbir fV hnormal x
  have h := QCartierPullback.pullbackToWeil_eq_of_positive_multiple π ⟨B, hB⟩ n hn A hA
  change QCartierPullback.pullbackToWeil π ⟨B, hB⟩ D = _
  rw [h]
  change (n : ℚ)⁻¹ * (S.cartierToWeilHom (pullbackHom π A) D : ℚ) = _
  rw [pullback_order S q hbir fV hnormal π v hcomm D x hD A]

/-- The original difference of the fixed canonical coefficient and the
original rational pullback coefficient is computed by actual Cartier
orders at the detected target point. The denominator is produced from
the original Q-Cartier membership, rather than assumed. -/
theorem exists_discrepancy_expression
    (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hD : q.base D.genericPoint = x.val) (KS : CartierDivisor S.toScheme)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    letI := point_isDiscreteValuationRing S q hbir fV hnormal x
    ∃ (n : ℕ) (_hn : 0 < n) (A : CartierDivisor X.toScheme),
      X.rationalCartierToWeilHom A = n • B ∧
      (S.cartierToWeilHom KS D : ℚ) - QCartierPullback.pullback π B hB D =
        (cartierOrderAt (targetIsomorphismOpen q).toScheme (divisor q hbir KS)
          (point S q hbir fV hnormal x) : ℚ) -
          (n : ℚ)⁻¹ * (cartierOrderAt (targetIsomorphismOpen q).toScheme
            (pullbackHom ((targetIsomorphismOpen q).ι ≫ v) A)
            (point S q hbir fV hnormal x) : ℚ) := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI := point_isDiscreteValuationRing S q hbir fV hnormal x
  obtain ⟨n, hn, A, hA⟩ := (X.qCartier_iff_exists_positive_multiple B).mp hB
  refine ⟨n, hn, A, hA, ?_⟩
  rw [divisor_order S q hbir fV hnormal D x hD KS,
    rational_pullback_order S q hbir fV hnormal X π v hcomm D x hD B hB n hn A hA]

end RationalOverTarget

end KltDP.Geometry.ProperBirationalCanonicalCoefficient
