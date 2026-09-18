import KltDP.Geometry.AffineBlowupRegularPairChartEquiv
import KltDP.Geometry.RegularPairBlowupResidualQuotient

/-!
# The original residual branch quotient in a regular-pair Rees chart

The original chart presentation identifies the actual fraction ideal
with the literal variable ideal. The residual quotient is therefore the
original principal base quotient R/(b), with the original coefficient
map preserved. Its prime ideal and exceptional nonmembership are derived
from the corresponding actual base-ring facts.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup Polynomial

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

def residualRelationIdeal : Ideal (relationRing I a b) :=
  Ideal.map (Ideal.Quotient.mk (Ideal.span {C (a : R) * X - C (b : R)})) (Ideal.span {X})

variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)})

theorem chartRelationEquiv_map_fraction :
    Ideal.map (chartRelationEquiv I a b ha hb hI).toRingHom
        (Ideal.span {chartFraction I a b}) = residualRelationIdeal I a b := by
  calc
    _ = Ideal.span {chartRelationEquiv I a b ha hb hI (chartFraction I a b)} := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    _ = Ideal.span {quotientFraction I a b} :=
      congrArg (fun z => Ideal.span {z}) (chartRelationEquiv_fraction I a b ha hb hI)
    _ = _ := by
      simp only [residualRelationIdeal, Ideal.map_span, Set.image_singleton, quotientFraction]

def residualPresentationEquiv :
    (chartRing I a ⧸ Ideal.span {chartFraction I a b}) ≃+*
      (relationRing I a b ⧸ residualRelationIdeal I a b) :=
  Ideal.quotientEquiv (Ideal.span {chartFraction I a b}) (residualRelationIdeal I a b)
    (chartRelationEquiv I a b ha hb hI)
    (chartRelationEquiv_map_fraction I a b ha hb hI).symm

theorem residualPresentationEquiv_mk (z : chartRing I a) :
    residualPresentationEquiv I a b ha hb hI
      (Ideal.Quotient.mk (Ideal.span {chartFraction I a b}) z) =
        Ideal.Quotient.mk (residualRelationIdeal I a b)
          (chartRelationEquiv I a b ha hb hI z) := rfl

/-- The actual fraction quotient, with the original base principal ideal. -/
def residualChartEquiv :
    (chartRing I a ⧸ Ideal.span {chartFraction I a b}) ≃+* R ⧸ Ideal.span {(b : R)} :=
  (residualPresentationEquiv I a b ha hb hI).trans
    (RegularPairBlowupRelation.residualQuotientEquiv (a : R) (b : R))

theorem residualChartEquiv_baseMap (r : R) :
    residualChartEquiv I a b ha hb hI
      (Ideal.Quotient.mk (Ideal.span {chartFraction I a b}) (chartBaseMap I a r)) =
        Ideal.Quotient.mk (Ideal.span {(b : R)}) r := by
  change RegularPairBlowupRelation.residualQuotientEquiv (a : R) (b : R)
    (residualPresentationEquiv I a b ha hb hI
      (Ideal.Quotient.mk (Ideal.span {chartFraction I a b}) (chartBaseMap I a r))) = _
  rw [residualPresentationEquiv_mk, chartRelationEquiv_baseMap]
  change RegularPairBlowupRelation.residualQuotientEquiv (a : R) (b : R)
    (DoubleQuot.quotQuotMk (Ideal.span {C (a : R) * X - C (b : R)})
      (Ideal.span {X}) (C r)) = _
  exact RegularPairBlowupRelation.residualQuotientEquiv_base (a : R) (b : R) r

def residualMap : chartRing I a →+* R ⧸ Ideal.span {(b : R)} :=
  (residualChartEquiv I a b ha hb hI).toRingHom.comp
    (Ideal.Quotient.mk (Ideal.span {chartFraction I a b}))

theorem residualMap_ker :
    RingHom.ker (residualMap I a b ha hb hI) = Ideal.span {chartFraction I a b} := by
  rw [residualMap,
    RingHom.ker_comp_of_injective _ (residualChartEquiv I a b ha hb hI).injective,
    Ideal.mk_ker]

theorem residualMap_baseMap (r : R) :
    residualMap I a b ha hb hI (chartBaseMap I a r) =
      Ideal.Quotient.mk (Ideal.span {(b : R)}) r :=
  residualChartEquiv_baseMap I a b ha hb hI r

include ha hb hI in
theorem residualIdeal_isPrime [(Ideal.span {(b : R)}).IsPrime] :
    (Ideal.span {chartFraction I a b}).IsPrime := by
  rw [← residualMap_ker I a b ha hb hI]
  exact RingHom.ker_isPrime _

include ha hb hI in
theorem parameter_not_mem_residual (hab : (a : R) ∉ Ideal.span {(b : R)}) :
    chartBaseMap I a (a : R) ∉ Ideal.span {chartFraction I a b} := by
  intro hx
  have hz : residualMap I a b ha hb hI (chartBaseMap I a (a : R)) = 0 := by
    apply RingHom.mem_ker.mp
    rw [residualMap_ker]
    exact hx
  rw [residualMap_baseMap] at hz
  exact hab (Ideal.Quotient.eq_zero_iff_mem.mp hz)

end KltDP.Geometry.AffineBlowupRegularPairChart
