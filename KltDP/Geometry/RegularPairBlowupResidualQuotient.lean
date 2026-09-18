import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Tactic.Ring

/-!
# The residual quotient of the literal regular-pair relation

Killing the original fraction variable in `R[T]/(f*T-g)` gives the
original principal quotient `R/(g)`. The existing polynomial quotient
equivalence preserves the original coefficient map and kills the actual
fraction. No regularity or chart-presentation assumption enters here.
-/

noncomputable section

namespace KltDP.Geometry.RegularPairBlowupRelation

open Polynomial

universe u

variable {R : Type u} [CommRing R] (f g : R)

theorem relation_sup_variable :
    Ideal.span {C f * X - C g} ⊔ Ideal.span {X} =
      Ideal.span {C g, X - C (0 : R)} := by
  calc
    _ = Ideal.span {C f * X - C g, X} := by rw [Ideal.span_insert]
    _ = Ideal.span {-C g + X * C f, X} := by
      rw [show C f * X - C g = -C g + X * C f by ring]
    _ = Ideal.span {-C g, X} := Ideal.span_pair_add_mul_left (C f)
    _ = _ := by
      simp only [Polynomial.C_0, sub_zero, Ideal.span_insert, Ideal.span_singleton_neg]

/-- Normalize the original quotient word before specializing its algebra equivalence. -/
private theorem quotient_word_coefficient
    (I J K : Ideal (Polynomial R)) (Q : Ideal R) (h : I ⊔ J = K)
    (e : (Polynomial R ⧸ K) ≃ₐ[R] (R ⧸ Q)) (r : R) :
    ((DoubleQuot.quotQuotEquivQuotSup I J).trans
      ((Ideal.quotEquivOfEq h).trans e.toRingEquiv))
        (DoubleQuot.quotQuotMk I J (C r)) = Ideal.Quotient.mk Q r := by
  simp only [RingEquiv.trans_apply,
    DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]
  exact e.commutes r

/-- A member of the actual final quotient ideal is killed by the original quotient word. -/
private theorem quotient_word_zero
    (I J K : Ideal (Polynomial R)) (Q : Ideal R) (h : I ⊔ J = K)
    (e : (Polynomial R ⧸ K) ≃+* (R ⧸ Q))
    (p : Polynomial R) (hp : p ∈ K) :
    ((DoubleQuot.quotQuotEquivQuotSup I J).trans
      ((Ideal.quotEquivOfEq h).trans e))
        (DoubleQuot.quotQuotMk I J p) = 0 := by
  simp only [RingEquiv.trans_apply,
    DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

/-- The literal residual double quotient, using the original coefficient quotient. -/
def residualQuotientEquiv :
    (Polynomial R ⧸ Ideal.span {C f * X - C g}) ⧸
        Ideal.map (Ideal.Quotient.mk (Ideal.span {C f * X - C g})) (Ideal.span {X}) ≃+*
      R ⧸ Ideal.span {g} :=
  (DoubleQuot.quotQuotEquivQuotSup
    (Ideal.span {C f * X - C g}) (Ideal.span {X})).trans
    ((Ideal.quotEquivOfEq (relation_sup_variable f g)).trans
      (Polynomial.quotientSpanCXSubCAlgEquiv g 0).toRingEquiv)

theorem residualQuotientEquiv_base (r : R) :
    residualQuotientEquiv f g
      (DoubleQuot.quotQuotMk (Ideal.span {C f * X - C g}) (Ideal.span {X}) (C r)) =
        Ideal.Quotient.mk (Ideal.span {g}) r := by
  exact quotient_word_coefficient _ _ _ _ (relation_sup_variable f g)
    (Polynomial.quotientSpanCXSubCAlgEquiv g 0) r

theorem residualQuotientEquiv_variable :
    residualQuotientEquiv f g
      (DoubleQuot.quotQuotMk (Ideal.span {C f * X - C g}) (Ideal.span {X}) X) = 0 := by
  apply quotient_word_zero _ _ _ _ (relation_sup_variable f g)
    (Polynomial.quotientSpanCXSubCAlgEquiv g 0).toRingEquiv X
  rw [Polynomial.C_0, sub_zero]
  exact Ideal.subset_span (by simp)

end KltDP.Geometry.RegularPairBlowupRelation
