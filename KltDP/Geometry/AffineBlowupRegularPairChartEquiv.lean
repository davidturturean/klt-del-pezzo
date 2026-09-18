import KltDP.Geometry.AffineBlowupRegularPairChartMap

/-!
# The original Rees chart for a regular pair has its actual relation presentation

Polynomial evaluation uses the original base map and original homogeneous
fraction. The reverse map is the already constructed original chart lift.
Polynomial and quotient extensionality give one inverse identity; the
existing original chart uniqueness theorem gives the other. Thus the
presentation is proved for the actual Rees chart, with normalized maps.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup Polynomial

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/-- Polynomial evaluation at the original base map and actual chart fraction. -/
def polynomialToChart : Polynomial R →+* chartRing I a :=
  Polynomial.eval₂RingHom (chartBaseMap I a) (chartFraction I a b)

theorem polynomialToChart_relation :
    polynomialToChart I a b (C (a : R) * X - C (b : R)) = 0 := by
  simp only [polynomialToChart, coe_eval₂RingHom, eval₂_sub, eval₂_mul,
    eval₂_C, eval₂_X, chartBaseMap_mul_chartFraction, sub_self]

/-- The relation quotient maps to the original chart by that literal evaluation. -/
def fromQuotient : relationRing I a b →+* chartRing I a :=
  Ideal.Quotient.lift _ (polynomialToChart I a b) (by
    change Ideal.span {C (a : R) * X - C (b : R)} ≤
      RingHom.ker (polynomialToChart I a b)
    apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr (polynomialToChart_relation I a b))

theorem fromQuotient_mk (P : Polynomial R) :
    fromQuotient I a b (Ideal.Quotient.mk _ P) = polynomialToChart I a b P := rfl

theorem fromQuotient_baseMap (r : R) :
    fromQuotient I a b (quotientBaseMap I a b r) = chartBaseMap I a r := by
  change fromQuotient I a b (Ideal.Quotient.mk _ (C r)) = _
  rw [fromQuotient_mk]
  exact Polynomial.eval₂_C _ _

theorem fromQuotient_fraction :
    fromQuotient I a b (quotientFraction I a b) = chartFraction I a b := by
  change fromQuotient I a b (Ideal.Quotient.mk _ X) = _
  rw [fromQuotient_mk]
  exact Polynomial.eval₂_X _ _

variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)})

theorem toQuotient_comp_fromQuotient :
    (toQuotient I a b ha hb hI).comp (fromQuotient I a b) =
      RingHom.id (relationRing I a b) := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change toQuotient I a b ha hb hI
      (fromQuotient I a b (quotientBaseMap I a b r)) = quotientBaseMap I a b r
    rw [fromQuotient_baseMap, toQuotient_baseMap]
  · change toQuotient I a b ha hb hI
      (fromQuotient I a b (quotientFraction I a b)) = quotientFraction I a b
    rw [fromQuotient_fraction, toQuotient_fraction]

theorem fromQuotient_comp_toQuotient :
    (fromQuotient I a b).comp (toQuotient I a b ha hb hI) =
      RingHom.id (chartRing I a) := by
  have hreg := chartBaseMap_equation_mem_nonZeroDivisors I a
  have hcenter := (map_chartBaseMap_ideal I a).le
  have hcomp : ((fromQuotient I a b).comp (toQuotient I a b ha hb hI)).comp
      (chartBaseMap I a) = chartBaseMap I a := by
    ext r
    simp only [RingHom.comp_apply, toQuotient_baseMap, fromQuotient_baseMap]
  exact (chartLift_unique I a (chartBaseMap I a) hreg hcenter
    ((fromQuotient I a b).comp (toQuotient I a b ha hb hI)) hcomp).trans
      (chartLift_unique I a (chartBaseMap I a) hreg hcenter
        (RingHom.id (chartRing I a)) (RingHom.id_comp _)).symm

/-- The actual Rees-chart presentation, with both inverse identities proved. -/
def chartRelationEquiv : chartRing I a ≃+* relationRing I a b where
  __ := toQuotient I a b ha hb hI
  invFun := fromQuotient I a b
  left_inv x := RingHom.congr_fun (fromQuotient_comp_toQuotient I a b ha hb hI) x
  right_inv x := RingHom.congr_fun (toQuotient_comp_fromQuotient I a b ha hb hI) x

theorem chartRelationEquiv_baseMap (r : R) :
    chartRelationEquiv I a b ha hb hI (chartBaseMap I a r) =
      quotientBaseMap I a b r := toQuotient_baseMap I a b ha hb hI r

theorem chartRelationEquiv_fraction :
    chartRelationEquiv I a b ha hb hI (chartFraction I a b) =
      quotientFraction I a b := toQuotient_fraction I a b ha hb hI

end KltDP.Geometry.AffineBlowupRegularPairChart
