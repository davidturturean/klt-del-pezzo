import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.Ring

/-!
# The exceptional quotient of the literal two-parameter relation

Killing the first parameter in `R[T]/(f*T-g)` gives the actual polynomial
ring over `R/(f,g)`. This uses the existing double-quotient and polynomial
quotient equivalences, with the original polynomial variable preserved.
It is independent of regularity and of the Rees-chart presentation proof.
-/

noncomputable section

namespace KltDP.Geometry.RegularPairBlowupRelation

open Polynomial

universe u

variable {R : Type u} [CommRing R] (f g : R)

theorem relation_sup_parameter :
    Ideal.span {C f * X - C g} ⊔ Ideal.span {C f} =
      Ideal.map C (Ideal.span {f, g}) := by
  calc
    _ = Ideal.span {C f * X - C g, C f} := by rw [Ideal.span_insert]
    _ = Ideal.span {-C g + C f * X, C f} := by
      rw [show C f * X - C g = -C g + C f * X by ring]
    _ = Ideal.span {-C g, C f} := Ideal.span_pair_add_mul_left X
    _ = Ideal.span {C f, C g} := by
      rw [Ideal.span_pair_comm, Ideal.span_insert, Ideal.span_singleton_neg,
        ← Ideal.span_insert]
    _ = _ := by rw [Ideal.map_span, Set.image_pair]

/-- The literal exceptional double quotient is the polynomial ring over
the original two-generator center quotient. -/
def exceptionalQuotientEquiv :
    (Polynomial R ⧸ Ideal.span {C f * X - C g}) ⧸
        Ideal.map (Ideal.Quotient.mk (Ideal.span {C f * X - C g})) (Ideal.span {C f}) ≃+*
      Polynomial (R ⧸ Ideal.span {f, g}) :=
  (DoubleQuot.quotQuotEquivQuotSup
    (Ideal.span {C f * X - C g}) (Ideal.span {C f})).trans
    ((Ideal.quotEquivOfEq (relation_sup_parameter f g)).trans
      (Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.span {f, g})).symm)

/-- The equivalence is induced by the original coefficient quotient map;
in particular it sends the original variable to the polynomial variable. -/
theorem exceptionalQuotientEquiv_mk (P : Polynomial R) :
    exceptionalQuotientEquiv f g
      (DoubleQuot.quotQuotMk (Ideal.span {C f * X - C g}) (Ideal.span {C f}) P) =
      P.map (Ideal.Quotient.mk (Ideal.span {f, g})) := by
  simp only [exceptionalQuotientEquiv, RingEquiv.trans_apply,
    DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk,
    Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk]

end KltDP.Geometry.RegularPairBlowupRelation
