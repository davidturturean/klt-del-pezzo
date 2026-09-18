import KltDP.Geometry.AffineBlowupRegularPairChartEquiv
import KltDP.Geometry.RegularPairBlowupExceptionalQuotient
import KltDP.Geometry.AffineBlowupConormal

/-!
# The original exceptional kernel in a regular-pair Rees chart

The proved chart presentation carries the original extended center ideal
to the literal first-parameter ideal in the relation quotient. Quotienting
therefore gives the original exceptional chart ring as `(R/I)[T]`, with
the actual coefficient map and actual homogeneous fraction preserved.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup Polynomial

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

def exceptionalRelationIdeal : Ideal (relationRing I a b) :=
  Ideal.map (Ideal.Quotient.mk (Ideal.span {C (a : R) * X - C (b : R)}))
    (Ideal.span {C (a : R)})

variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)})

/-- The original exceptional kernel ideal has its literal image under the
normalized actual Rees-chart presentation. -/
theorem chartRelationEquiv_map_center :
    Ideal.map (chartRelationEquiv I a b ha hb hI).toRingHom (chartCenterIdeal I a) =
      exceptionalRelationIdeal I a b := by
  calc
    _ = Ideal.span {chartRelationEquiv I a b ha hb hI (chartBaseMap I a (a : R))} := by
      rw [chartCenterIdeal, map_chartBaseMap_ideal, Ideal.map_span, Set.image_singleton]
      rfl
    _ = Ideal.span {quotientBaseMap I a b (a : R)} :=
      congrArg (fun z => Ideal.span {z}) (chartRelationEquiv_baseMap I a b ha hb hI (a : R))
    _ = _ := by
      simp only [exceptionalRelationIdeal, Ideal.map_span, Set.image_singleton,
        quotientBaseMap, RingHom.comp_apply]

def exceptionalPresentationEquiv :
    exceptionalChartRing I a ≃+* (relationRing I a b ⧸ exceptionalRelationIdeal I a b) :=
  Ideal.quotientEquiv (chartCenterIdeal I a) (exceptionalRelationIdeal I a b)
    (chartRelationEquiv I a b ha hb hI) (chartRelationEquiv_map_center I a b ha hb hI).symm

theorem exceptionalPresentationEquiv_mk (z : chartRing I a) :
    exceptionalPresentationEquiv I a b ha hb hI (Ideal.Quotient.mk (chartCenterIdeal I a) z) =
      Ideal.Quotient.mk (exceptionalRelationIdeal I a b)
        (chartRelationEquiv I a b ha hb hI z) := rfl

/-- The actual original exceptional chart ring, over the actual original
center quotient. This is a derived isomorphism, not a replacement chart. -/
def exceptionalChartEquiv : exceptionalChartRing I a ≃+* Polynomial (R ⧸ I) :=
  (exceptionalPresentationEquiv I a b ha hb hI).trans
    ((RegularPairBlowupRelation.exceptionalQuotientEquiv (a : R) (b : R)).trans
      (Polynomial.mapEquiv (Ideal.quotEquivOfEq hI.symm)))

/-- The actual exceptional fraction becomes the polynomial variable. -/
theorem exceptionalChartEquiv_fraction :
    exceptionalChartEquiv I a b ha hb hI
      (Ideal.Quotient.mk (chartCenterIdeal I a) (chartFraction I a b)) = X := by
  change (Polynomial.mapEquiv (Ideal.quotEquivOfEq hI.symm))
    (RegularPairBlowupRelation.exceptionalQuotientEquiv (a : R) (b : R)
      (exceptionalPresentationEquiv I a b ha hb hI
        (Ideal.Quotient.mk (chartCenterIdeal I a) (chartFraction I a b)))) = X
  rw [exceptionalPresentationEquiv_mk, chartRelationEquiv_fraction]
  change (Polynomial.mapEquiv (Ideal.quotEquivOfEq hI.symm))
    (RegularPairBlowupRelation.exceptionalQuotientEquiv (a : R) (b : R)
      (DoubleQuot.quotQuotMk (Ideal.span {C (a : R) * X - C (b : R)})
        (Ideal.span {C (a : R)}) X)) = X
  rw [RegularPairBlowupRelation.exceptionalQuotientEquiv_mk, Polynomial.map_X]
  change Polynomial.map (Ideal.quotEquivOfEq hI.symm).toRingHom X = X
  exact Polynomial.map_X _

/-- The original base coefficients reduce by the original center ideal. -/
theorem exceptionalChartEquiv_baseMap (r : R) :
    exceptionalChartEquiv I a b ha hb hI
      (Ideal.Quotient.mk (chartCenterIdeal I a) (chartBaseMap I a r)) =
        C (Ideal.Quotient.mk I r) := by
  change (Polynomial.mapEquiv (Ideal.quotEquivOfEq hI.symm))
    (RegularPairBlowupRelation.exceptionalQuotientEquiv (a : R) (b : R)
      (exceptionalPresentationEquiv I a b ha hb hI
        (Ideal.Quotient.mk (chartCenterIdeal I a) (chartBaseMap I a r)))) = _
  rw [exceptionalPresentationEquiv_mk, chartRelationEquiv_baseMap]
  change (Polynomial.mapEquiv (Ideal.quotEquivOfEq hI.symm))
    (RegularPairBlowupRelation.exceptionalQuotientEquiv (a : R) (b : R)
      (DoubleQuot.quotQuotMk (Ideal.span {C (a : R) * X - C (b : R)})
        (Ideal.span {C (a : R)}) (C r))) = _
  rw [RegularPairBlowupRelation.exceptionalQuotientEquiv_mk, Polynomial.map_C]
  change Polynomial.map (Ideal.quotEquivOfEq hI.symm).toRingHom
    (C (Ideal.Quotient.mk (Ideal.span {(a : R), (b : R)}) r)) = _
  rw [Polynomial.map_C]
  exact congrArg C (Ideal.quotEquivOfEq_mk hI.symm r)

end KltDP.Geometry.AffineBlowupRegularPairChart
