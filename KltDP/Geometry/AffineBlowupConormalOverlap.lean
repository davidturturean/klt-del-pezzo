import KltDP.Geometry.AffineBlowupConormal
import KltDP.RingTheory.ConormalRestriction

/-!
# Conormal transition on the actual intersection of Rees charts

Mathlib's homogeneous localization at `(aT)(bT)` is the actual intersection
of the two Proj charts. Its two restriction maps are the pinned `awayMap`
maps. They localize at the respective chart ratios. The existing center
ideals and their conormal modules restrict along these actual maps.

The defining equations satisfy `d_b = (b/a) d_a`. The ratio and its image
in the exceptional quotient are units, and the conormal coordinate change
is proved with exactly that factor. No overlap ring, compatibility matrix,
or line-bundle gluing is assumed as input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace KltDP.Geometry.AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/-- The pinned homogeneous localization at the actual product of chart elements. -/
abbrev conormalOverlapRing := HomogeneousLocalization.Away (ReesGrading.component I)
  (degreeOne I a * degreeOne I b)

/-- Actual restriction from the first Rees chart to its intersection with the second. -/
def conormalOverlapLeft : chartRing I a →+* conormalOverlapRing I a b :=
  HomogeneousLocalization.awayMap (ReesGrading.component I) (degreeOne_mem I b) rfl

/-- Actual restriction from the second chart to the same product chart. -/
def conormalOverlapRight : chartRing I b →+* conormalOverlapRing I a b :=
  HomogeneousLocalization.awayMap (ReesGrading.component I) (degreeOne_mem I a)
    (mul_comm _ _)

/-- The product chart is the actual categorical intersection of the chart immersions. -/
def conormalOverlapIso : pullback (chartι I a) (chartι I b) ≅
    Spec (CommRingCat.of (conormalOverlapRing I a b)) :=
  Proj.pullbackAwayιIso (ReesGrading.component I) (degreeOne_mem I a) (by decide)
    (degreeOne_mem I b) (by decide) rfl

/-- The left ring restriction is the actual first overlap projection. -/
theorem conormalOverlapIso_hom_left :
    (conormalOverlapIso I a b).hom ≫
      Spec.map (CommRingCat.ofHom (conormalOverlapLeft I a b)) =
        pullback.fst (chartι I a) (chartι I b) :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left _ _ _ _ _ _

/-- The right ring restriction is the actual second overlap projection. -/
theorem conormalOverlapIso_hom_right :
    (conormalOverlapIso I a b).hom ≫
      Spec.map (CommRingCat.ofHom (conormalOverlapRight I a b)) =
        pullback.snd (chartι I a) (chartι I b) :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right _ _ _ _ _ _

/-- The actual degree-zero base map into the product localization. -/
def conormalOverlapBaseMap : R →+* conormalOverlapRing I a b :=
  (HomogeneousLocalization.fromZeroRingHom (ReesGrading.component I)
    (Submonoid.powers (degreeOne I a * degreeOne I b))).comp
      (algebraMap R (ReesGrading.component I 0))

@[simp]
theorem conormalOverlapLeft_baseMap (r : R) :
    conormalOverlapLeft I a b (chartBaseMap I a r) = conormalOverlapBaseMap I a b r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

@[simp]
theorem conormalOverlapRight_baseMap (r : R) :
    conormalOverlapRight I a b (chartBaseMap I b r) = conormalOverlapBaseMap I a b r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

/-- The pinned localization element is exactly the existing chart ratio. -/
theorem conormalOverlap_localizationElem :
    HomogeneousLocalization.Away.isLocalizationElem
      (degreeOne_mem I a) (degreeOne_mem I b) = chartFraction I a b := by
  simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one,
    chartFraction, chartMonomialFraction, degreeOne]

/-- The actual left restriction localizes at `b/a`. -/
theorem conormalOverlapLeft_isLocalization :
    letI := (conormalOverlapLeft I a b).toAlgebra
    IsLocalization.Away (chartFraction I a b) (conormalOverlapRing I a b) := by
  letI := (conormalOverlapLeft I a b).toAlgebra
  have h := HomogeneousLocalization.Away.isLocalization_mul
    (degreeOne_mem I a) (degreeOne_mem I b) (rfl :
      degreeOne I a * degreeOne I b = degreeOne I a * degreeOne I b) (by decide)
  rw [conormalOverlap_localizationElem] at h
  exact h

/-- The actual right restriction localizes at `a/b`. -/
theorem conormalOverlapRight_isLocalization :
    letI := (conormalOverlapRight I a b).toAlgebra
    IsLocalization.Away (chartFraction I b a) (conormalOverlapRing I a b) := by
  letI := (conormalOverlapRight I a b).toAlgebra
  have h := HomogeneousLocalization.Away.isLocalization_mul
    (degreeOne_mem I b) (degreeOne_mem I a)
    (mul_comm (degreeOne I a) (degreeOne I b)) (by decide)
  rw [conormalOverlap_localizationElem] at h
  exact h

/-- The actual ratio on the intersection. -/
def conormalOverlapRatio : conormalOverlapRing I a b :=
  conormalOverlapLeft I a b (chartFraction I a b)

/-- The ratio is a unit by the pinned localization theorem. -/
theorem conormalOverlapRatio_isUnit : IsUnit (conormalOverlapRatio I a b) := by
  letI := (conormalOverlapLeft I a b).toAlgebra
  letI : IsLocalization.Away (chartFraction I a b) (conormalOverlapRing I a b) :=
    conormalOverlapLeft_isLocalization I a b
  exact IsLocalization.Away.algebraMap_isUnit (chartFraction I a b)

/-- The actual extended center ideal on the product chart. -/
def conormalOverlapIdeal : Ideal (conormalOverlapRing I a b) :=
  Ideal.map (conormalOverlapBaseMap I a b) I

theorem conormalOverlapLeft_map_ideal :
    Ideal.map (conormalOverlapLeft I a b) (chartCenterIdeal I a) =
      conormalOverlapIdeal I a b := by
  change Ideal.map (conormalOverlapLeft I a b) (Ideal.map (chartBaseMap I a) I) =
    Ideal.map (conormalOverlapBaseMap I a b) I
  rw [Ideal.map_map]
  have h : (conormalOverlapLeft I a b).comp (chartBaseMap I a) =
      conormalOverlapBaseMap I a b := RingHom.ext (conormalOverlapLeft_baseMap I a b)
  rw [h]

theorem conormalOverlapRight_map_ideal :
    Ideal.map (conormalOverlapRight I a b) (chartCenterIdeal I b) =
      conormalOverlapIdeal I a b := by
  change Ideal.map (conormalOverlapRight I a b) (Ideal.map (chartBaseMap I b) I) =
    Ideal.map (conormalOverlapBaseMap I a b) I
  rw [Ideal.map_map]
  have h : (conormalOverlapRight I a b).comp (chartBaseMap I b) =
      conormalOverlapBaseMap I a b := RingHom.ext (conormalOverlapRight_baseMap I a b)
  rw [h]

theorem conormalOverlapLeft_ideal_le : chartCenterIdeal I a ≤
    (conormalOverlapIdeal I a b).comap (conormalOverlapLeft I a b) :=
  Ideal.map_le_iff_le_comap.mp (conormalOverlapLeft_map_ideal I a b).le

theorem conormalOverlapRight_ideal_le : chartCenterIdeal I b ≤
    (conormalOverlapIdeal I a b).comap (conormalOverlapRight I a b) :=
  Ideal.map_le_iff_le_comap.mp (conormalOverlapRight_map_ideal I a b).le

/-- Restriction of the actual conormal from the first chart. -/
def conormalOverlapMapLeft : (chartCenterIdeal I a).Cotangent →ₛₗ[
    Ideal.quotientMap (conormalOverlapIdeal I a b) (conormalOverlapLeft I a b)
      (conormalOverlapLeft_ideal_le I a b)] (conormalOverlapIdeal I a b).Cotangent :=
  KltDP.RingTheory.conormalMap _ _ _ (conormalOverlapLeft_ideal_le I a b)

/-- Restriction of the actual conormal from the second chart. -/
def conormalOverlapMapRight : (chartCenterIdeal I b).Cotangent →ₛₗ[
    Ideal.quotientMap (conormalOverlapIdeal I a b) (conormalOverlapRight I a b)
      (conormalOverlapRight_ideal_le I a b)] (conormalOverlapIdeal I a b).Cotangent :=
  KltDP.RingTheory.conormalMap _ _ _ (conormalOverlapRight_ideal_le I a b)

/-- The equation from the first chart, in the actual overlap ideal. -/
def conormalOverlapEquationLeft : conormalOverlapIdeal I a b :=
  ⟨conormalOverlapBaseMap I a b (a : R),
    Ideal.mem_map_of_mem (conormalOverlapBaseMap I a b) a.property⟩

/-- The equation from the second chart, in the same actual ideal. -/
def conormalOverlapEquationRight : conormalOverlapIdeal I a b :=
  ⟨conormalOverlapBaseMap I a b (b : R),
    Ideal.mem_map_of_mem (conormalOverlapBaseMap I a b) b.property⟩

/-- The first equation stays regular under the actual overlap localization. -/
theorem conormalOverlapEquationLeft_regular :
    (conormalOverlapEquationLeft I a b : conormalOverlapRing I a b) ∈
      nonZeroDivisors (conormalOverlapRing I a b) := by
  letI := (conormalOverlapLeft I a b).toAlgebra
  letI : IsLocalization.Away (chartFraction I a b) (conormalOverlapRing I a b) :=
    conormalOverlapLeft_isLocalization I a b
  have h := IsLocalization.nonZeroDivisors_le_comap
    (Submonoid.powers (chartFraction I a b)) (conormalOverlapRing I a b)
    (chartBaseMap_equation_mem_nonZeroDivisors I a)
  change conormalOverlapLeft I a b (chartBaseMap I a (a : R)) ∈
    nonZeroDivisors (conormalOverlapRing I a b) at h
  rw [conormalOverlapLeft_baseMap] at h
  exact h

/-- The first equation generates the actual overlap center ideal. -/
theorem span_conormalOverlapEquationLeft :
    Ideal.span {(conormalOverlapEquationLeft I a b : conormalOverlapRing I a b)} =
      conormalOverlapIdeal I a b := by
  have h := conormalOverlapLeft_map_ideal I a b
  rw [chartCenterIdeal, map_chartBaseMap_ideal, Ideal.map_span,
    Set.image_singleton, conormalOverlapLeft_baseMap] at h
  exact h

/-- The actual overlap conormal coordinates in the first chart frame. -/
def conormalOverlapEquiv :
    (conormalOverlapRing I a b ⧸ conormalOverlapIdeal I a b) ≃ₗ[
      conormalOverlapRing I a b ⧸ conormalOverlapIdeal I a b]
        (conormalOverlapIdeal I a b).Cotangent :=
  KltDP.RingTheory.principalConormalEquiv _ (conormalOverlapEquationLeft I a b)
    (span_conormalOverlapEquationLeft I a b) (conormalOverlapEquationLeft_regular I a b)

/-- The actual equations differ by precisely `b/a`. -/
theorem conormalOverlap_equation_transition :
    (conormalOverlapEquationRight I a b : conormalOverlapRing I a b) =
      conormalOverlapRatio I a b * conormalOverlapEquationLeft I a b := by
  have h := congrArg (conormalOverlapLeft I a b) (chartBaseMap_mul_chartFraction I a b)
  simp only [map_mul, conormalOverlapLeft_baseMap] at h
  exact h.symm.trans (mul_comm _ _)

/-- The ratio remains a unit on the actual exceptional quotient of the overlap. -/
theorem conormalOverlapRatio_quotient_isUnit :
    IsUnit (Ideal.Quotient.mk (conormalOverlapIdeal I a b) (conormalOverlapRatio I a b)) :=
  (conormalOverlapRatio_isUnit I a b).map (Ideal.Quotient.mk (conormalOverlapIdeal I a b))

/-- The first conormal generator restricts to its actual equation class. -/
theorem conormalOverlapMapLeft_generator :
    conormalOverlapMapLeft I a b
      ((chartCenterIdeal I a).toCotangent (chartCenterEquation I a)) =
        (conormalOverlapIdeal I a b).toCotangent (conormalOverlapEquationLeft I a b) := by
  change (conormalOverlapIdeal I a b).toCotangent _ = _
  apply congrArg (conormalOverlapIdeal I a b).toCotangent
  exact Subtype.ext (conormalOverlapLeft_baseMap I a b (a : R))

/-- The second conormal generator restricts to its actual equation class. -/
theorem conormalOverlapMapRight_generator :
    conormalOverlapMapRight I a b
      ((chartCenterIdeal I b).toCotangent (chartCenterEquation I b)) =
        (conormalOverlapIdeal I a b).toCotangent (conormalOverlapEquationRight I a b) := by
  change (conormalOverlapIdeal I a b).toCotangent _ = _
  apply congrArg (conormalOverlapIdeal I a b).toCotangent
  exact Subtype.ext (conormalOverlapRight_baseMap I a b (b : R))

/-- The actual conormal frames obey the unit-ratio transition formula.
This is an equality in the existing overlap conormal module. -/
theorem conormalOverlap_generator_transition :
    conormalOverlapMapRight I a b
      ((chartCenterIdeal I b).toCotangent (chartCenterEquation I b)) =
        Ideal.Quotient.mk (conormalOverlapIdeal I a b) (conormalOverlapRatio I a b) •
          conormalOverlapMapLeft I a b
            ((chartCenterIdeal I a).toCotangent (chartCenterEquation I a)) := by
  rw [conormalOverlapMapLeft_generator, conormalOverlapMapRight_generator]
  exact KltDP.RingTheory.toCotangent_eq_quotient_smul_of_eq_mul
    (conormalOverlapIdeal I a b) (conormalOverlapEquationLeft I a b)
    (conormalOverlapEquationRight I a b) (conormalOverlapRatio I a b)
    (conormalOverlap_equation_transition I a b)

/-- Normal coordinates transform by evaluation on the actual changed
conormal generator, with the same quotient ratio. -/
theorem conormalOverlap_normal_evaluation_transition
    (ℓ : Module.Dual (conormalOverlapRing I a b ⧸ conormalOverlapIdeal I a b)
      (conormalOverlapIdeal I a b).Cotangent) :
    ℓ (conormalOverlapMapRight I a b
      ((chartCenterIdeal I b).toCotangent (chartCenterEquation I b))) =
        Ideal.Quotient.mk (conormalOverlapIdeal I a b) (conormalOverlapRatio I a b) *
          ℓ (conormalOverlapMapLeft I a b
            ((chartCenterIdeal I a).toCotangent (chartCenterEquation I a))) := by
  rw [conormalOverlap_generator_transition]
  exact ℓ.map_smul _ _

end KltDP.Geometry.AffineBlowup
