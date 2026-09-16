import KltDP.Geometry.AffineBlowupChartCenter
import KltDP.RingTheory.RegularPrincipalConormal
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual exceptional charts and their conormal modules

On every actual Rees chart, the extended center is a regular principal
ideal. Its quotient defines an actual closed immersion into that chart,
and its conormal module is explicitly free on the defining equation.
The dual normal module is identified by evaluation on the same class.

These are affine local constructions. No global exceptional closed
subscheme, conormal sheaf gluing, projective-space identification, or
normal-bundle degree is assumed or asserted by this module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)

/-- The actual image of the base center ideal in the Rees chart. -/
def chartCenterIdeal : Ideal (chartRing I a) := Ideal.map (chartBaseMap I a) I

/-- The actual regular equation, as an element of the actual center ideal. -/
def chartCenterEquation : chartCenterIdeal I a :=
  ⟨chartBaseMap I a (a : R), Ideal.mem_map_of_mem (chartBaseMap I a) a.property⟩

/-- The equation generates the actual extended center. -/
theorem span_chartCenterEquation :
    Ideal.span {(chartCenterEquation I a : chartRing I a)} = chartCenterIdeal I a :=
  (map_chartBaseMap_ideal I a).symm

/-- Regularity is derived from the Rees chart injection, not assumed. -/
theorem chartCenterEquation_regular :
    (chartCenterEquation I a : chartRing I a) ∈ nonZeroDivisors (chartRing I a) :=
  chartBaseMap_equation_mem_nonZeroDivisors I a

/-- The actual quotient ring of the center on this Rees chart. -/
abbrev exceptionalChartRing := chartRing I a ⧸ chartCenterIdeal I a

/-- The affine scheme cut out by the actual extended center ideal. -/
def exceptionalChart : Scheme := Spec (CommRingCat.of (exceptionalChartRing I a))

/-- The canonical closed immersion into the actual Rees chart. -/
def exceptionalChartInclusion : exceptionalChart I a ⟶
    Spec (CommRingCat.of (chartRing I a)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartCenterIdeal I a)))

instance : IsClosedImmersion (exceptionalChartInclusion I a) := by
  unfold exceptionalChartInclusion
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (chartCenterIdeal I a))) Ideal.Quotient.mk_surjective

/-- The actual local exceptional chart maps into the full blowup. -/
def exceptionalChartToBlowup : exceptionalChart I a ⟶ scheme I :=
  exceptionalChartInclusion I a ≫ chartι I a

/-- The local exceptional morphism retains the canonical map to the base. -/
@[simp]
theorem exceptionalChartToBlowup_toSpec :
    exceptionalChartToBlowup I a ≫ toSpec I =
      Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (chartCenterIdeal I a)).comp (chartBaseMap I a))) := by
  have hchart : chartι I a ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := chartι_toSpec I a
  rw [exceptionalChartToBlowup, Category.assoc, hchart, exceptionalChartInclusion,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The local exceptional ring receives the actual quotient of the base
by its center: every center element is killed by the chart quotient. -/
def exceptionalChartBaseQuotientMap : (R ⧸ I) →+* exceptionalChartRing I a :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (chartCenterIdeal I a)).comp (chartBaseMap I a))
    (fun r hr => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (chartBaseMap I a) hr))

/-- The induced quotient map has the exact base-ring formula. -/
@[simp]
theorem exceptionalChartBaseQuotientMap_mk (r : R) :
    exceptionalChartBaseQuotientMap I a (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (chartCenterIdeal I a) (chartBaseMap I a r) := rfl

/-- The actual exceptional chart maps to the original center scheme. -/
def exceptionalChartToCenter : exceptionalChart I a ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
  Spec.map (CommRingCat.ofHom (exceptionalChartBaseQuotientMap I a))

/-- The morphism to the center commutes with the original affine base maps. -/
theorem exceptionalChartToCenter_toSpec :
    exceptionalChartToCenter I a ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      exceptionalChartToBlowup I a ≫ toSpec I := by
  rw [exceptionalChartToCenter, ← Spec.map_comp, exceptionalChartToBlowup_toSpec]
  congr 1

/-- The actual conormal module of the chart's defining ideal. -/
abbrev exceptionalChartConormal := (chartCenterIdeal I a).Cotangent

/-- Multiplication by the actual equation class trivializes the conormal
module over the actual quotient ring of the exceptional chart. -/
def exceptionalChartConormalEquiv :
    exceptionalChartRing I a ≃ₗ[exceptionalChartRing I a] exceptionalChartConormal I a :=
  KltDP.RingTheory.principalConormalEquiv (chartCenterIdeal I a) (chartCenterEquation I a)
    (span_chartCenterEquation I a) (chartCenterEquation_regular I a)

/-- The conormal generator is the class of the actual chart equation. -/
@[simp]
theorem exceptionalChartConormalEquiv_one :
    exceptionalChartConormalEquiv I a 1 =
      (chartCenterIdeal I a).toCotangent (chartCenterEquation I a) :=
  KltDP.RingTheory.principalConormalEquiv_one _ _ _ _

/-- An actual singleton basis of the chart conormal module. -/
def exceptionalChartConormalBasis :
    Basis PUnit (exceptionalChartRing I a) (exceptionalChartConormal I a) :=
  KltDP.RingTheory.principalConormalBasis (chartCenterIdeal I a) (chartCenterEquation I a)
    (span_chartCenterEquation I a) (chartCenterEquation_regular I a)

/-- The local normal module is the quotient-linear dual of the conormal. -/
abbrev exceptionalChartNormal :=
  Module.Dual (exceptionalChartRing I a) (exceptionalChartConormal I a)

/-- Evaluation on the actual equation class trivializes the local normal module. -/
def exceptionalChartNormalEquiv :
    exceptionalChartNormal I a ≃ₗ[exceptionalChartRing I a] exceptionalChartRing I a :=
  KltDP.RingTheory.principalNormalEquiv (chartCenterIdeal I a) (chartCenterEquation I a)
    (span_chartCenterEquation I a) (chartCenterEquation_regular I a)

/-- The normal coordinate is exactly evaluation on the defining equation class. -/
@[simp]
theorem exceptionalChartNormalEquiv_apply (ℓ : exceptionalChartNormal I a) :
    exceptionalChartNormalEquiv I a ℓ =
      ℓ ((chartCenterIdeal I a).toCotangent (chartCenterEquation I a)) :=
  KltDP.RingTheory.principalNormalEquiv_apply _ _ _ _ ℓ

end KltDP.Geometry.AffineBlowup
