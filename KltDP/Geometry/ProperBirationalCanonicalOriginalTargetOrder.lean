import KltDP.Geometry.ProperBirationalCanonicalCoefficient

/-!
# The detected rational pullback order on the original target model

Restriction does not change the original Cartier pullback order at a
corresponding DVR point. Thus the fixed-source discrepancy expression
uses the original model V and the original map v for its rational term.
The canonical term remains the explicitly constructed fixed-KS choice
on the original target big open.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperBirationalCanonicalOriginalTargetOrder

open OpenImmersionRational DominantCartierPullback
open ProperBirationalCanonicalCoefficient ProperBirationalCanonicalRestriction

attribute [local instance] integralSchemeStalk_isDomain

local instance openGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (e : Y ⟶ Z) [IsOpenImmersion e] : GenericPointPreserving e :=
  ⟨genericPoint_eq_of_isOpenImmersion e⟩

private theorem order_pullback_under_open
    {W V X : Scheme.{u}} [IsIntegral W] [IsIntegral V] [IsIntegral X]
    (i : W ⟶ V) [IsOpenImmersion i] (v : V ⟶ X) [GenericPointPreserving v]
    (w : W) (x : V) (hw : i.base w = x)
    [IsDiscreteValuationRing (W.presheaf.stalk w)]
    [IsDiscreteValuationRing (V.presheaf.stalk x)] (A : CartierDivisor X) :
    cartierOrderAt W (pullbackHom (i ≫ v) A) w =
      cartierOrderAt V (pullbackHom v A) x := by
  rw [pullbackHom_comp, AddMonoidHom.comp_apply, pullbackHom_eq_cartierRestrictionHom]
  exact cartierOrderAt_cartierRestrictionHom i (pullbackHom v A) w x hw

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)
    {V : Scheme.{u}} [IsIntegral V] (q : S.toScheme ⟶ V) [IsProper q]
    (hbir : IsBirationalScheme q) (fV : V ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fV] (hnormal : IsNormalScheme V)

/-- The original target-open Cartier order is exactly the Cartier order
on the original model V, along the original map v. -/
theorem target_pullback_order {X : Scheme.{u}} [IsIntegral X]
    (v : V ⟶ X) [GenericPointPreserving v]
    (x : CodimensionOnePoint V) (A : CartierDivisor X) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    letI := normalFiniteTypePoint_isDiscreteValuationRing fV hnormal x
    letI := point_isDiscreteValuationRing S q hbir fV hnormal x
    cartierOrderAt (targetIsomorphismOpen q).toScheme
        (pullbackHom ((targetIsomorphismOpen q).ι ≫ v) A)
        (point S q hbir fV hnormal x) = cartierOrderAt V (pullbackHom v A) x.val := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI := normalFiniteTypePoint_isDiscreteValuationRing fV hnormal x
  letI := point_isDiscreteValuationRing S q hbir fV hnormal x
  exact order_pullback_under_open (targetIsomorphismOpen q).ι v
    (point S q hbir fV hnormal x) x.val rfl A

variable [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (π : S.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    [GenericPointPreserving π] [GenericPointPreserving v]
    (hcomm : q ≫ v = π)

include hbir hcomm

/-- The rational pullback coefficient is computed directly on the original V. -/
theorem rational_pullback_order
    (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hD : q.base D.genericPoint = x.val)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • B) :
    letI := normalFiniteTypePoint_isDiscreteValuationRing fV hnormal x
    QCartierPullback.pullback π B hB D =
      (n : ℚ)⁻¹ * (cartierOrderAt V (pullbackHom v A) x.val : ℚ) := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI := normalFiniteTypePoint_isDiscreteValuationRing fV hnormal x
  letI := point_isDiscreteValuationRing S q hbir fV hnormal x
  have h := ProperBirationalCanonicalCoefficient.rational_pullback_order
    S q hbir fV hnormal X π v hcomm D x hD B hB n hn A hA
  rw [target_pullback_order S q hbir fV hnormal v x A] at h
  exact h

/-- Produce the actual numerator and compare the original coefficient
difference with the fixed-KS canonical order and the original V pullback order. -/
theorem exists_discrepancy_expression
    (D : S.PrimeCurve) (x : CodimensionOnePoint V)
    (hD : q.base D.genericPoint = x.val) (KS : CartierDivisor S.toScheme)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    letI := normalFiniteTypePoint_isDiscreteValuationRing fV hnormal x
    letI := point_isDiscreteValuationRing S q hbir fV hnormal x
    ∃ (n : ℕ) (_hn : 0 < n) (A : CartierDivisor X.toScheme),
      X.rationalCartierToWeilHom A = n • B ∧
      (S.cartierToWeilHom KS D : ℚ) - QCartierPullback.pullback π B hB D =
        (cartierOrderAt (targetIsomorphismOpen q).toScheme (divisor q hbir KS)
          (point S q hbir fV hnormal x) : ℚ) -
          (n : ℚ)⁻¹ * (cartierOrderAt V (pullbackHom v A) x.val : ℚ) := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI := normalFiniteTypePoint_isDiscreteValuationRing fV hnormal x
  letI := point_isDiscreteValuationRing S q hbir fV hnormal x
  obtain ⟨n, hn, A, hA⟩ := (X.qCartier_iff_exists_positive_multiple B).mp hB
  refine ⟨n, hn, A, hA, ?_⟩
  rw [divisor_order S q hbir fV hnormal D x hD KS,
    rational_pullback_order S q hbir fV hnormal X π v hcomm D x hD B hB n hn A hA]

end KltDP.Geometry.ProperBirationalCanonicalOriginalTargetOrder
