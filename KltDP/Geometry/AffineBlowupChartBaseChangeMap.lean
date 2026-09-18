import KltDP.Geometry.AffineBlowupLift
import KltDP.Geometry.AffineBlowupChartCenter

/-!
# The actual map of Rees charts under a ring map

Use the original chart lift into the chart of the extended ideal. The
regularity and principal-center hypotheses of that lift are the already
proved properties of the original target Rees chart. No chart comparison is
assumed. Both base functions and the actual degree-one fractions are preserved.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (I : Ideal R) (φ : R →+* S)

/-- The original element of the extended center ideal. -/
def mappedElement (a : I) : Ideal.map φ I :=
  ⟨φ (a : R), Ideal.mem_map_of_mem φ a.property⟩

variable (a : I)

/-- The original composite base map into the target homogeneous chart. -/
def baseMap : R →+* chartRing (Ideal.map φ I) (mappedElement I φ a) :=
  (chartBaseMap (Ideal.map φ I) (mappedElement I φ a)).comp φ

theorem baseMap_regular :
    baseMap I φ a (a : R) ∈
      nonZeroDivisors (chartRing (Ideal.map φ I) (mappedElement I φ a)) :=
  chartBaseMap_equation_mem_nonZeroDivisors (Ideal.map φ I) (mappedElement I φ a)

theorem mappedCenter_span :
    Ideal.map (baseMap I φ a) I = Ideal.span {baseMap I φ a (a : R)} := by
  change Ideal.map ((chartBaseMap (Ideal.map φ I) (mappedElement I φ a)).comp φ) I = _
  rw [← Ideal.map_map]
  exact map_chartBaseMap_ideal (Ideal.map φ I) (mappedElement I φ a)

/-- The actual universal chart lift, with all lift conditions derived. -/
def chartMap : chartRing I a →+* chartRing (Ideal.map φ I) (mappedElement I φ a) :=
  chartLift I a (baseMap I φ a) (baseMap_regular I φ a) (mappedCenter_span I φ a).le

theorem chartMap_baseMap (r : R) :
    chartMap I φ a (chartBaseMap I a r) = baseMap I φ a r :=
  chartLift_baseMap I a (baseMap I φ a) (baseMap_regular I φ a)
    (mappedCenter_span I φ a).le r

/-- The original homogeneous fraction maps to the corresponding actual fraction. -/
theorem chartMap_fraction (b : I) :
    chartMap I φ a (chartFraction I a b) =
      chartFraction (Ideal.map φ I) (mappedElement I φ a) (mappedElement I φ b) := by
  apply (mul_cancel_left_mem_nonZeroDivisors (baseMap_regular I φ a)).mp
  have h := congrArg (chartMap I φ a) (chartBaseMap_mul_chartFraction I a b)
  rw [map_mul, chartMap_baseMap, chartMap_baseMap] at h
  exact h.trans (chartBaseMap_mul_chartFraction (Ideal.map φ I)
    (mappedElement I φ a) (mappedElement I φ b)).symm

end KltDP.Geometry.AffineBlowupChartBaseChange
