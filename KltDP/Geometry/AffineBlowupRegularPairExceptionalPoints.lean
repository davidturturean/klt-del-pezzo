import KltDP.Geometry.AffineBlowupRegularPairClosedPoint
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# All original chart points above the centre

The proved exceptional quotient is the polynomial ring over the original
centre field. Its prime ideals are zero or maximal. Consequently every
original chart prime containing the centre ideal is its actual generic
exceptional ideal or a maximal ideal. No algebraic-closure, smoothness,
dimension, or point-classification premise is used.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)
variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)})

attribute [local instance] Ideal.Quotient.field

include ha hb hI in
/-- The original exceptional chart has only its generic point and closed points. -/
theorem exceptional_prime_eq_center_or_maximal [I.IsMaximal]
    (P : Ideal (chartRing I a)) [P.IsPrime]
    (hcenter : chartCenterIdeal I a ≤ P) :
    P = chartCenterIdeal I a ∨ P.IsMaximal := by
  let φ := exceptionalCoordinateMap I a b ha hb hI
  have hφ : Function.Surjective φ := exceptionalCoordinateMap_surjective I a b ha hb hI
  have hker : RingHom.ker φ = chartCenterIdeal I a :=
    exceptionalCoordinateMap_ker I a b ha hb hI
  have hP : (Ideal.map φ P).comap φ = P := by
    rw [Ideal.comap_map_of_surjective' φ hφ, hker, sup_eq_left.mpr hcenter]
  by_cases hzero : Ideal.map φ P = ⊥
  · have hkerP : RingHom.ker φ = P :=
      (congrArg (Ideal.comap φ) hzero).symm.trans hP
    exact Or.inl (hkerP.symm.trans hker)
  · letI : (Ideal.map φ P).IsPrime :=
      Ideal.map_isPrime_of_surjective hφ (hker.le.trans hcenter)
    letI : (Ideal.map φ P).IsMaximal := IsPrime.to_maximal_ideal hzero
    have hmax : ((Ideal.map φ P).comap φ).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective φ hφ
    exact Or.inr (hP ▸ hmax)

end KltDP.Geometry.AffineBlowupRegularPairChart
