import KltDP.Geometry.AffineBlowupConormalOverlap
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The conormal cocycle on actual triple Rees-chart intersections

The ring on the triple intersection is the existing homogeneous
localization at `(aT * bT) * cT`. Its restrictions from the three double
intersections are the pinned `awayMap` maps, and the actual Proj pullback
theorem identifies its spectrum with the iterated chart intersection.

The ratios satisfy `(c/a) = (b/a) * (c/b)` by cancellation of the actual
regular equation `a` after restriction. Their images are units in the
exceptional quotient and satisfy the same cocycle there. This proves the
coordinate cocycle for the actual conormal module; no gluing datum or
global invertible sheaf is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace KltDP.Geometry.AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b c : I)

/-- The actual product-chart immersion for the first two indices. -/
def conormalOverlapι : Spec (CommRingCat.of (conormalOverlapRing I a b)) ⟶ scheme I :=
  Proj.awayι (ReesGrading.component I) (degreeOne I a * degreeOne I b)
    (SetLike.mul_mem_graded (degreeOne_mem I a) (degreeOne_mem I b)) (by decide)

/-- This product chart is the already constructed categorical overlap. -/
theorem conormalOverlapIso_hom_ι :
    (conormalOverlapIso I a b).hom ≫ conormalOverlapι I a b =
      pullback.fst (chartι I a) (chartι I b) ≫ chartι I a :=
  Proj.pullbackAwayιIso_hom_awayι _ _ _ _ _ _

/-- The actual homogeneous localization on the triple intersection. -/
abbrev conormalTripleRing := HomogeneousLocalization.Away (ReesGrading.component I)
  ((degreeOne I a * degreeOne I b) * degreeOne I c)

/-- Restriction from the `ab` double intersection. -/
def conormalTripleFromAB : conormalOverlapRing I a b →+* conormalTripleRing I a b c :=
  HomogeneousLocalization.awayMap (ReesGrading.component I) (degreeOne_mem I c) rfl

/-- Restriction from the `ac` double intersection to the same actual ring. -/
def conormalTripleFromAC : conormalOverlapRing I a c →+* conormalTripleRing I a b c :=
  HomogeneousLocalization.awayMap (ReesGrading.component I) (degreeOne_mem I b)
    (by ac_rfl)

/-- Restriction from the `bc` double intersection to the same actual ring. -/
def conormalTripleFromBC : conormalOverlapRing I b c →+* conormalTripleRing I a b c :=
  HomogeneousLocalization.awayMap (ReesGrading.component I) (degreeOne_mem I a)
    (by ac_rfl)

/-- Restriction from the third chart, for the actual iterated pullback. -/
def conormalTripleFromC : chartRing I c →+* conormalTripleRing I a b c :=
  HomogeneousLocalization.awayMap (ReesGrading.component I)
    (SetLike.mul_mem_graded (degreeOne_mem I a) (degreeOne_mem I b))
    (mul_comm _ _)

/-- The triple ring is the actual intersection of the `ab` product chart
and the `c` chart. Combined with `conormalOverlapIso_hom_ι`, this is an
actual iterated chart intersection, not a separately postulated overlap. -/
def conormalTripleIso : pullback (conormalOverlapι I a b) (chartι I c) ≅
    Spec (CommRingCat.of (conormalTripleRing I a b c)) :=
  Proj.pullbackAwayιIso (ReesGrading.component I)
    (SetLike.mul_mem_graded (degreeOne_mem I a) (degreeOne_mem I b)) (by decide)
    (degreeOne_mem I c) (by decide) rfl

/-- The restriction from `ab` is the actual first projection. -/
theorem conormalTripleIso_hom_ab :
    (conormalTripleIso I a b c).hom ≫
      Spec.map (CommRingCat.ofHom (conormalTripleFromAB I a b c)) =
        pullback.fst (conormalOverlapι I a b) (chartι I c) :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left _ _ _ _ _ _

/-- The restriction from `c` is the actual second projection. -/
theorem conormalTripleIso_hom_c :
    (conormalTripleIso I a b c).hom ≫
      Spec.map (CommRingCat.ofHom (conormalTripleFromC I a b c)) =
        pullback.snd (conormalOverlapι I a b) (chartι I c) :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right _ _ _ _ _ _

/-- The actual base map into the triple homogeneous localization. -/
def conormalTripleBaseMap : R →+* conormalTripleRing I a b c :=
  (HomogeneousLocalization.fromZeroRingHom (ReesGrading.component I)
    (Submonoid.powers ((degreeOne I a * degreeOne I b) * degreeOne I c))).comp
      (algebraMap R (ReesGrading.component I 0))

@[simp]
theorem conormalTripleFromAB_baseMap (r : R) :
    conormalTripleFromAB I a b c (conormalOverlapBaseMap I a b r) =
      conormalTripleBaseMap I a b c r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

@[simp]
theorem conormalTripleFromAC_baseMap (r : R) :
    conormalTripleFromAC I a b c (conormalOverlapBaseMap I a c r) =
      conormalTripleBaseMap I a b c r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

@[simp]
theorem conormalTripleFromBC_baseMap (r : R) :
    conormalTripleFromBC I a b c (conormalOverlapBaseMap I b c r) =
      conormalTripleBaseMap I a b c r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

/-- The restriction from `ab` is an actual localization, at the pinned
homogeneous localization element `(cT)^2 / ((aT)(bT))`. -/
theorem conormalTripleFromAB_isLocalization :
    letI := (conormalTripleFromAB I a b c).toAlgebra
    IsLocalization.Away (HomogeneousLocalization.Away.isLocalizationElem
      (SetLike.mul_mem_graded (degreeOne_mem I a) (degreeOne_mem I b))
      (degreeOne_mem I c)) (conormalTripleRing I a b c) := by
  letI := (conormalTripleFromAB I a b c).toAlgebra
  exact HomogeneousLocalization.Away.isLocalization_mul
    (SetLike.mul_mem_graded (degreeOne_mem I a) (degreeOne_mem I b))
    (degreeOne_mem I c) rfl (by decide)

/-- The extended center ideal on the actual triple chart. -/
def conormalTripleIdeal : Ideal (conormalTripleRing I a b c) :=
  Ideal.map (conormalTripleBaseMap I a b c) I

/-- Restriction carries the actual double-intersection center to the
actual triple-intersection center. -/
theorem conormalTripleFromAB_map_ideal :
    Ideal.map (conormalTripleFromAB I a b c) (conormalOverlapIdeal I a b) =
      conormalTripleIdeal I a b c := by
  change Ideal.map (conormalTripleFromAB I a b c)
    (Ideal.map (conormalOverlapBaseMap I a b) I) =
      Ideal.map (conormalTripleBaseMap I a b c) I
  rw [Ideal.map_map]
  have h : (conormalTripleFromAB I a b c).comp (conormalOverlapBaseMap I a b) =
      conormalTripleBaseMap I a b c := RingHom.ext (conormalTripleFromAB_baseMap I a b c)
  rw [h]

/-- The original center element, as an actual equation in the triple ideal. -/
def conormalTripleEquation (d : I) : conormalTripleIdeal I a b c :=
  ⟨conormalTripleBaseMap I a b c (d : R),
    Ideal.mem_map_of_mem (conormalTripleBaseMap I a b c) d.property⟩

/-- The first center equation remains regular on the triple localization. -/
theorem conormalTripleEquationA_regular :
    (conormalTripleEquation I a b c a : conormalTripleRing I a b c) ∈
      nonZeroDivisors (conormalTripleRing I a b c) := by
  let t := HomogeneousLocalization.Away.isLocalizationElem
    (SetLike.mul_mem_graded (degreeOne_mem I a) (degreeOne_mem I b))
    (degreeOne_mem I c)
  letI := (conormalTripleFromAB I a b c).toAlgebra
  letI : IsLocalization.Away t (conormalTripleRing I a b c) :=
    conormalTripleFromAB_isLocalization I a b c
  have h := IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers t)
    (conormalTripleRing I a b c) (conormalOverlapEquationLeft_regular I a b)
  change conormalTripleFromAB I a b c (conormalOverlapBaseMap I a b (a : R)) ∈
    nonZeroDivisors (conormalTripleRing I a b c) at h
  rw [conormalTripleFromAB_baseMap] at h
  exact h

/-- The first equation generates the actual triple-intersection center. -/
theorem span_conormalTripleEquationA :
    Ideal.span {(conormalTripleEquation I a b c a : conormalTripleRing I a b c)} =
      conormalTripleIdeal I a b c := by
  have h := conormalTripleFromAB_map_ideal I a b c
  rw [← span_conormalOverlapEquationLeft I a b, Ideal.map_span, Set.image_singleton] at h
  change Ideal.span {conormalTripleFromAB I a b c
    (conormalOverlapBaseMap I a b (a : R))} = conormalTripleIdeal I a b c at h
  rw [conormalTripleFromAB_baseMap] at h
  exact h

/-- Actual free coordinates on the triple-intersection conormal. -/
def conormalTripleEquiv :
    (conormalTripleRing I a b c ⧸ conormalTripleIdeal I a b c) ≃ₗ[
      conormalTripleRing I a b c ⧸ conormalTripleIdeal I a b c]
        (conormalTripleIdeal I a b c).Cotangent :=
  KltDP.RingTheory.principalConormalEquiv _ (conormalTripleEquation I a b c a)
    (span_conormalTripleEquationA I a b c) (conormalTripleEquationA_regular I a b c)

/-- The `b/a` transition after the actual double-to-triple restriction. -/
def conormalTripleRatioAB : conormalTripleRing I a b c :=
  conormalTripleFromAB I a b c (conormalOverlapRatio I a b)

/-- The `c/a` transition after the actual double-to-triple restriction. -/
def conormalTripleRatioAC : conormalTripleRing I a b c :=
  conormalTripleFromAC I a b c (conormalOverlapRatio I a c)

/-- The `c/b` transition after the actual double-to-triple restriction. -/
def conormalTripleRatioBC : conormalTripleRing I a b c :=
  conormalTripleFromBC I a b c (conormalOverlapRatio I b c)

theorem conormalTripleRatioAB_isUnit : IsUnit (conormalTripleRatioAB I a b c) :=
  (conormalOverlapRatio_isUnit I a b).map (conormalTripleFromAB I a b c)

theorem conormalTripleRatioAC_isUnit : IsUnit (conormalTripleRatioAC I a b c) :=
  (conormalOverlapRatio_isUnit I a c).map (conormalTripleFromAC I a b c)

theorem conormalTripleRatioBC_isUnit : IsUnit (conormalTripleRatioBC I a b c) :=
  (conormalOverlapRatio_isUnit I b c).map (conormalTripleFromBC I a b c)

theorem conormalTriple_equation_ab :
    (conormalTripleEquation I a b c b : conormalTripleRing I a b c) =
      conormalTripleRatioAB I a b c * conormalTripleEquation I a b c a := by
  have h := congrArg (conormalTripleFromAB I a b c) (conormalOverlap_equation_transition I a b)
  simp only [map_mul] at h
  change conormalTripleFromAB I a b c (conormalOverlapBaseMap I a b (b : R)) =
    conormalTripleRatioAB I a b c *
      conormalTripleFromAB I a b c (conormalOverlapBaseMap I a b (a : R)) at h
  simpa only [conormalTripleFromAB_baseMap] using h

theorem conormalTriple_equation_ac :
    (conormalTripleEquation I a b c c : conormalTripleRing I a b c) =
      conormalTripleRatioAC I a b c * conormalTripleEquation I a b c a := by
  have h := congrArg (conormalTripleFromAC I a b c) (conormalOverlap_equation_transition I a c)
  simp only [map_mul] at h
  change conormalTripleFromAC I a b c (conormalOverlapBaseMap I a c (c : R)) =
    conormalTripleRatioAC I a b c *
      conormalTripleFromAC I a b c (conormalOverlapBaseMap I a c (a : R)) at h
  simpa only [conormalTripleFromAC_baseMap] using h

theorem conormalTriple_equation_bc :
    (conormalTripleEquation I a b c c : conormalTripleRing I a b c) =
      conormalTripleRatioBC I a b c * conormalTripleEquation I a b c b := by
  have h := congrArg (conormalTripleFromBC I a b c) (conormalOverlap_equation_transition I b c)
  simp only [map_mul] at h
  change conormalTripleFromBC I a b c (conormalOverlapBaseMap I b c (c : R)) =
    conormalTripleRatioBC I a b c *
      conormalTripleFromBC I a b c (conormalOverlapBaseMap I b c (b : R)) at h
  simpa only [conormalTripleFromBC_baseMap] using h

/-- The exact unit-ratio cocycle on the actual triple intersection. The
proof cancels a derived regular center equation, with no domain hypothesis. -/
theorem conormalTriple_ratio_cocycle :
    conormalTripleRatioAC I a b c =
      conormalTripleRatioAB I a b c * conormalTripleRatioBC I a b c := by
  apply (mul_cancel_right_mem_nonZeroDivisors (conormalTripleEquationA_regular I a b c)).mp
  calc
    conormalTripleRatioAC I a b c * conormalTripleEquation I a b c a =
        (conormalTripleEquation I a b c c : conormalTripleRing I a b c) :=
      (conormalTriple_equation_ac I a b c).symm
    _ = conormalTripleRatioBC I a b c * conormalTripleEquation I a b c b :=
      conormalTriple_equation_bc I a b c
    _ = conormalTripleRatioBC I a b c *
        (conormalTripleRatioAB I a b c * conormalTripleEquation I a b c a) :=
      congrArg (conormalTripleRatioBC I a b c * ·) (conormalTriple_equation_ab I a b c)
    _ = (conormalTripleRatioAB I a b c * conormalTripleRatioBC I a b c) *
        conormalTripleEquation I a b c a := by ac_rfl

/-- The cocycle descends to the actual exceptional quotient ring. -/
theorem conormalTriple_quotient_ratio_cocycle :
    Ideal.Quotient.mk (conormalTripleIdeal I a b c) (conormalTripleRatioAC I a b c) =
      Ideal.Quotient.mk (conormalTripleIdeal I a b c) (conormalTripleRatioAB I a b c) *
        Ideal.Quotient.mk (conormalTripleIdeal I a b c) (conormalTripleRatioBC I a b c) := by
  rw [conormalTriple_ratio_cocycle, map_mul]

/-- Each transition coefficient stays a unit on the actual exceptional
triple intersection. -/
theorem conormalTriple_quotient_ratios_isUnit :
    IsUnit (Ideal.Quotient.mk (conormalTripleIdeal I a b c) (conormalTripleRatioAB I a b c)) ∧
      IsUnit (Ideal.Quotient.mk (conormalTripleIdeal I a b c) (conormalTripleRatioAC I a b c)) ∧
        IsUnit (Ideal.Quotient.mk (conormalTripleIdeal I a b c) (conormalTripleRatioBC I a b c)) :=
  ⟨(conormalTripleRatioAB_isUnit I a b c).map (Ideal.Quotient.mk _),
    (conormalTripleRatioAC_isUnit I a b c).map (Ideal.Quotient.mk _),
    (conormalTripleRatioBC_isUnit I a b c).map (Ideal.Quotient.mk _)⟩

/-- The actual conormal generator satisfies the composite transition law. -/
theorem conormalTriple_generator_cocycle :
    (conormalTripleIdeal I a b c).toCotangent (conormalTripleEquation I a b c c) =
      (Ideal.Quotient.mk (conormalTripleIdeal I a b c) (conormalTripleRatioAB I a b c) *
        Ideal.Quotient.mk (conormalTripleIdeal I a b c) (conormalTripleRatioBC I a b c)) •
          (conormalTripleIdeal I a b c).toCotangent (conormalTripleEquation I a b c a) := by
  rw [← conormalTriple_quotient_ratio_cocycle]
  exact KltDP.RingTheory.toCotangent_eq_quotient_smul_of_eq_mul
    (conormalTripleIdeal I a b c) (conormalTripleEquation I a b c a)
    (conormalTripleEquation I a b c c) (conormalTripleRatioAC I a b c)
    (conormalTriple_equation_ac I a b c)

end KltDP.Geometry.AffineBlowup
