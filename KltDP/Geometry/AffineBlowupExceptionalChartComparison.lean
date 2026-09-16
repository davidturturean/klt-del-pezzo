import KltDP.Geometry.AffineBlowupCoordinateIso
import KltDP.Geometry.AffineBlowupExceptionalFiber
import KltDP.Geometry.GluedConormalPullbackFrame
import KltDP.RingTheory.ConormalRestriction

/-!
# Original Rees quotient charts and ideal-sheaf quotient charts

The original Rees chart and the canonical spectrum of sections on its open
range are compared using the pinned open-immersion range isomorphism and
fully faithful Spec. The actual extended ideals are transported by that
ring equivalence, so the induced quotient comparison preserves every
numerator and the original regular defining equation before quotienting.

The resulting chart map agrees with the existing map to the actual glued
exceptional scheme. The actual semilinear cotangent map preserves the
equation class and both original principal-coordinate frames. No chart,
frame, conormal, or P1 identification is assumed. Inter-chart sheaf-frame
naturality and the global P1 transition remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)

/-- The original Rees chart's actual affine open range. -/
def chartAffineOpen : (scheme I).affineOpens :=
  ⟨(chartι I a).opensRange, isAffineOpen_opensRange (chartι I a)⟩

/-- Canonical sections coordinates and the original Rees coordinates
have the same actual open immersion into the blowup. -/
def chartSectionSchemeIso :
    Spec Γ(scheme I, (chartAffineOpen I a).1) ≅
      Spec (CommRingCat.of (chartRing I a)) :=
  IsOpenImmersion.isoOfRangeEq (chartAffineOpen I a).2.fromSpec (chartι I a) (by
    rw [(chartAffineOpen I a).2.range_fromSpec]
    rfl)

theorem chartSectionSchemeIso_hom_fac :
    (chartSectionSchemeIso I a).hom ≫ chartι I a = (chartAffineOpen I a).2.fromSpec :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The ring equivalence is extracted from this actual scheme isomorphism,
using the already defined fully faithful Spec adapter. -/
def chartSectionsEquiv :
    chartRing I a ≃+* Γ(scheme I, (chartAffineOpen I a).1) :=
  (coordinateRingIso (chartSectionSchemeIso I a)).commRingCatIsoToRingEquiv

theorem chartSectionsEquiv_toRingHom :
    (chartSectionsEquiv I a).toRingHom =
      (Spec.preimage (chartSectionSchemeIso I a).hom).hom := rfl

/-- The comparison retains the actual base-ring map. -/
theorem chartSectionsEquiv_baseMap :
    (Spec.preimage ((chartAffineOpen I a).2.fromSpec ≫ toSpec I)).hom =
      (chartSectionsEquiv I a).toRingHom.comp (chartBaseMap I a) := by
  have hchart : chartι I a ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := chartι_toSpec I a
  have hpre : Spec.preimage ((chartAffineOpen I a).2.fromSpec ≫ toSpec I) =
      CommRingCat.ofHom (chartBaseMap I a) ≫
        Spec.preimage (chartSectionSchemeIso I a).hom := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage,
      ← hchart, ← Category.assoc, chartSectionSchemeIso_hom_fac]
  exact congrArg CommRingCat.Hom.hom hpre

/-- The original ideal-sheaf chart ideal is the image of the original
Rees chart ideal, not a separately selected principal ideal. -/
theorem exceptionalIdeal_chartAffineOpen :
    (exceptionalIdeal I).ideal (chartAffineOpen I a) =
      Ideal.map (chartSectionsEquiv I a).toRingHom (chartCenterIdeal I a) := by
  rw [exceptionalIdeal, extendedCenter_ideal, chartSectionsEquiv_baseMap,
    chartCenterIdeal, Ideal.map_map]

/-- The section equation is the image of the original Rees equation
before passage to either quotient ring. -/
def chartEquationSection : Γ(scheme I, (chartAffineOpen I a).1) :=
  chartSectionsEquiv I a (chartCenterEquation I a)

theorem exceptionalIdeal_chartEquationSection :
    (exceptionalIdeal I).ideal (chartAffineOpen I a) =
      Ideal.span {chartEquationSection I a} := by
  rw [exceptionalIdeal_chartAffineOpen, ← span_chartCenterEquation I a,
    Ideal.map_span, Set.image_singleton]
  rfl

/-- Regularity is derived from the original Rees equation and the actual
coordinate isomorphism. It is not an additional chart hypothesis. -/
theorem chartEquationSection_regular :
    chartEquationSection I a ∈
      nonZeroDivisors Γ(scheme I, (chartAffineOpen I a).1) := by
  apply mem_nonZeroDivisors_of_injective (f := (chartSectionsEquiv I a).symm)
    (chartSectionsEquiv I a).symm.injective
  change (chartSectionsEquiv I a).symm
      (chartSectionsEquiv I a (chartCenterEquation I a)) ∈ nonZeroDivisors (chartRing I a)
  rw [RingEquiv.symm_apply_apply]
  exact chartCenterEquation_regular I a

/-- The actual quotient-ring isomorphism induced by the original ambient
coordinate isomorphism and the derived equality of extended ideals. -/
def exceptionalChartQuotientEquiv :
    exceptionalChartRing I a ≃+*
      (Γ(scheme I, (chartAffineOpen I a).1) ⧸
        (exceptionalIdeal I).ideal (chartAffineOpen I a)) :=
  Ideal.quotientEquiv (chartCenterIdeal I a)
    ((exceptionalIdeal I).ideal (chartAffineOpen I a))
    (chartSectionsEquiv I a) (exceptionalIdeal_chartAffineOpen I a)

/-- Every original quotient numerator is preserved through its actual
ambient coordinate map. -/
theorem exceptionalChartQuotientEquiv_mk (r : chartRing I a) :
    exceptionalChartQuotientEquiv I a (Ideal.Quotient.mk (chartCenterIdeal I a) r) =
      Ideal.Quotient.mk ((exceptionalIdeal I).ideal (chartAffineOpen I a))
        (chartSectionsEquiv I a r) := rfl

/-- The original exceptional Rees chart is the original ideal-sheaf
quotient chart on its actual ambient open range. -/
def exceptionalGluedChartIso : exceptionalChart I a ≅
    (exceptionalIdeal I).glueDataObj (chartAffineOpen I a) :=
  Scheme.Spec.mapIso (exceptionalChartQuotientEquiv I a).symm.toCommRingCatIso.op

/-- The quotient comparison retains both original ambient affine maps. -/
theorem exceptionalGluedChartIso_hom_quotient :
    (exceptionalGluedChartIso I a).hom ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk ((exceptionalIdeal I).ideal (chartAffineOpen I a)))) =
      exceptionalChartInclusion I a ≫ (chartSectionSchemeIso I a).inv := by
  change Spec.map (CommRingCat.ofHom (exceptionalChartQuotientEquiv I a).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((exceptionalIdeal I).ideal (chartAffineOpen I a)))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartCenterIdeal I a))) ≫
      (chartSectionSchemeIso I a).inv
  rw [← Spec.map_preimage (chartSectionSchemeIso I a).inv,
    ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  rfl

/-- The actual quotient-chart inclusion into the blowup is preserved. -/
theorem exceptionalGluedChartIso_hom_toBlowup :
    (exceptionalGluedChartIso I a).hom ≫
        (exceptionalIdeal I).glueDataObjι (chartAffineOpen I a) ≫
          (chartAffineOpen I a).1.ι = exceptionalChartToBlowup I a := by
  rw [(exceptionalIdeal I).glueDataObjι_ι,
    ← Category.assoc, exceptionalGluedChartIso_hom_quotient,
    ← chartSectionSchemeIso_hom_fac I a]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, exceptionalChartToBlowup]

/-- The comparison reaches the same original glued exceptional chart
as the previously constructed categorical fiber comparison. -/
theorem exceptionalGluedChartIso_hom_toExceptional :
    (exceptionalGluedChartIso I a).hom ≫
        (exceptionalIdeal I).glueData.ι (chartAffineOpen I a) =
      exceptionalChartToFiber I a ≫ (exceptionalFiberIso I).inv := by
  apply (cancel_mono (exceptionalι I)).mp
  simp only [Category.assoc, exceptionalFiberIso_inv_ι, exceptionalChartToFiber_ι]
  change (exceptionalGluedChartIso I a).hom ≫
      ((exceptionalIdeal I).glueData.ι (chartAffineOpen I a) ≫
        (exceptionalIdeal I).gluedTo) = _
  rw [(exceptionalIdeal I).ι_gluedTo]
  exact exceptionalGluedChartIso_hom_toBlowup I a

/-- The same ambient coordinate map induces the actual semilinear map
of ideal cotangent modules. -/
def exceptionalChartConormalMap :
    (chartCenterIdeal I a).Cotangent →ₛₗ[(exceptionalChartQuotientEquiv I a).toRingHom]
      ((exceptionalIdeal I).ideal (chartAffineOpen I a)).Cotangent :=
  KltDP.RingTheory.conormalMap (chartCenterIdeal I a)
    ((exceptionalIdeal I).ideal (chartAffineOpen I a))
    (chartSectionsEquiv I a).toRingHom (by
      rw [exceptionalIdeal_chartAffineOpen]
      exact Ideal.le_comap_map)

/-- The original equation class maps to the exact ideal-sheaf equation
class used by the existing global conormal frame. -/
theorem exceptionalChartConormalMap_equation :
    exceptionalChartConormalMap I a
        ((chartCenterIdeal I a).toCotangent (chartCenterEquation I a)) =
      ((exceptionalIdeal I).ideal (chartAffineOpen I a)).toCotangent
        (gluedAffineIdealEquation (exceptionalIdeal I) (chartAffineOpen I a)
          (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)) := rfl

/-- The entire original principal-coordinate frame, not just its zero
image in the quotient ring, is preserved by the actual cotangent map. -/
theorem exceptionalChartConormalMap_frame (q : exceptionalChartRing I a) :
    exceptionalChartConormalMap I a (exceptionalChartConormalEquiv I a q) =
      gluedAffineCotangentEquiv (exceptionalIdeal I) (chartAffineOpen I a)
        (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a)
        (chartEquationSection_regular I a) (exceptionalChartQuotientEquiv I a q) := by
  have h := KltDP.RingTheory.conormalMap_principalConormalEquiv
    (chartCenterIdeal I a) ((exceptionalIdeal I).ideal (chartAffineOpen I a))
    (chartSectionsEquiv I a).toRingHom
    (show chartCenterIdeal I a ≤
      (((exceptionalIdeal I).ideal (chartAffineOpen I a)).comap
        (chartSectionsEquiv I a).toRingHom) from by
      rw [exceptionalIdeal_chartAffineOpen]
      exact Ideal.le_comap_map)
    (chartCenterEquation I a) (span_chartCenterEquation I a) (chartCenterEquation_regular I a)
    (gluedAffineIdealEquation (exceptionalIdeal I) (chartAffineOpen I a)
      (chartEquationSection I a) (exceptionalIdeal_chartEquationSection I a))
    (exceptionalIdeal_chartEquationSection I a).symm (chartEquationSection_regular I a)
    1 (by simp only [one_mul]; rfl) q
  simpa only [map_one, mul_one] using h

end KltDP.Geometry.AffineBlowup
