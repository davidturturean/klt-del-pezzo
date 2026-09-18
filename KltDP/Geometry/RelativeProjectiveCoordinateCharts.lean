/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveBasicOpenBaseChange
import KltDP.Geometry.ProjectiveSpaceCoordinateCharts

/-!
# The actual coordinate cover over any commutative coefficient ring

This extends the selected coordinate-chart, coordinate-swap and overlap proofs
from fields to commutative rings. The proofs used here require no domain or
normality. Every ring, scheme, base map and overlap is the original polynomial
Proj construction; the generic homogeneous-localization equivalence is reused.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (n : ℕ)

/-- The actual degree-zero localization at coordinate `i`. -/
abbrev coordinateChartRing (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading R n)
    (MvPolynomial.X i : homogeneousRing R n)

/-- Swapping `X₀` and `Xᵢ` gives an actual equivalence from the first
coordinate chart ring to the `i`th chart ring. -/
def firstChartEquivCoordinateChart (i : Fin (n + 1)) :
    chartRing R n ≃+* coordinateChartRing R n i := by
  refine homogeneousLocalizationRingEquiv (grading R n) (grading R n)
    (Submonoid.powers (coordinate R n))
    (Submonoid.powers (MvPolynomial.X i : homogeneousRing R n))
    (MvPolynomial.renameEquiv R (Equiv.swap 0 i)).toRingEquiv ?_ ?_ ?_ ?_
  · apply Submonoid.powers_le.mpr
    change MvPolynomial.rename (Equiv.swap 0 i) (MvPolynomial.X 0) ∈
      Submonoid.powers (MvPolynomial.X i : homogeneousRing R n)
    rw [MvPolynomial.rename_X, Equiv.swap_apply_left]
    exact Submonoid.mem_powers _
  · apply Submonoid.powers_le.mpr
    change MvPolynomial.rename (Equiv.swap 0 i) (MvPolynomial.X i) ∈
      Submonoid.powers (MvPolynomial.X 0 : homogeneousRing R n)
    rw [MvPolynomial.rename_X, Equiv.swap_apply_right]
    exact Submonoid.mem_powers _
  · intro d a ha
    change (MvPolynomial.rename (Equiv.swap 0 i) a).IsHomogeneous d
    exact (show a.IsHomogeneous d from ha).rename_isHomogeneous
  · intro d a ha
    change (MvPolynomial.rename (Equiv.swap 0 i) a).IsHomogeneous d
    exact (show a.IsHomogeneous d from ha).rename_isHomogeneous

/-- A polynomial in the irrelevant ideal has zero constant coefficient.
Every supported monomial therefore contains a variable, so the variables
span the irrelevant ideal. -/
theorem irrelevant_le_span_coordinates :
    (HomogeneousIdeal.irrelevant (grading R n)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → homogeneousRing R n)) := by
  classical
  intro p hp
  have hproj : GradedRing.proj (grading R n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at hproj
  change (MvPolynomial.decomposition.decompose' p 0 : homogeneousRing R n) = 0 at hproj
  rw [MvPolynomial.decomposition.decompose'_apply] at hproj
  rw [MvPolynomial.homogeneousComponent_zero] at hproj
  have hzero : MvPolynomial.coeff 0 p = 0 := by
    apply MvPolynomial.C_injective (Fin (n + 1)) R
    simpa only [map_zero] using hproj
  rw [← Set.image_univ (f := (MvPolynomial.X : Fin (n + 1) → homogeneousRing R n)),
    MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hmzero : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.mp hm) hzero
  by_contra! h
  apply hmzero
  ext i
  simpa using h i

/-- The actual coordinate basic opens cover projective space. -/
theorem iSup_coordinateStandardOpen :
    ⨆ i : Fin (n + 1), Proj.basicOpen (grading R n) (MvPolynomial.X i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (grading R n) MvPolynomial.X
    (irrelevant_le_span_coordinates R n)

/-- The usual finite standard affine cover, built from the actual `Proj`
chart immersions and the proved spanning statement. -/
def standardAffineCover : (freeProjectivization R n).AffineOpenCover :=
  Proj.openCoverOfISupEqTop (grading R n)
    (MvPolynomial.X : Fin (n + 1) → homogeneousRing R n)
    (m := fun _ ↦ 1) (fun i ↦ MvPolynomial.isHomogeneous_X R i)
    (fun _ ↦ Nat.zero_lt_one) (irrelevant_le_span_coordinates R n)

theorem coordinate_mem (i : Fin (n + 1)) :
    (MvPolynomial.X i : homogeneousRing R n) ∈ grading R n 1 :=
  MvPolynomial.isHomogeneous_X R i

/-- The `Proj` chart of the coordinate `z_i`. -/
def coordinateChartMorphism (i : Fin (n + 1)) :
    Spec (CommRingCat.of (coordinateChartRing R n i)) ⟶ freeProjectivization R n :=
  Proj.awayι (grading R n) (MvPolynomial.X i) (coordinate_mem R n i) Nat.one_pos

instance coordinateChartMorphism_isOpenImmersion (i : Fin (n + 1)) :
    IsOpenImmersion (coordinateChartMorphism R n i) := by
  unfold coordinateChartMorphism
  infer_instance

theorem coordinateChartMorphism_opensRange (i : Fin (n + 1)) :
    (coordinateChartMorphism R n i).opensRange =
      Proj.basicOpen (grading R n) (MvPolynomial.X i) :=
  Proj.opensRange_awayι (grading R n) (MvPolynomial.X i) (coordinate_mem R n i) Nat.one_pos

/-- The chart of `z₀` is the accepted `chartMorphism`. -/
theorem coordinateChartMorphism_zero : coordinateChartMorphism R n 0 =
    (standardChartIsoSpec R n).inv ≫ (standardOpen R n).ι := rfl

/-- The base constants in the chart ring of `z_i`. -/
def coordinateChartConstants (i : Fin (n + 1)) : R →+* coordinateChartRing R n i :=
  (HomogeneousLocalization.fromZeroRingHom (grading R n)
    (Submonoid.powers (MvPolynomial.X i : homogeneousRing R n))).comp
    (baseConstants R n)

/-- Every coordinate chart is over `R`. -/
theorem coordinateChartMorphism_over_base (i : Fin (n + 1)) :
    coordinateChartMorphism R n i ≫ freeProjectivizationToBase R n =
      Spec.map (CommRingCat.ofHom (coordinateChartConstants R n i)) := by
  unfold coordinateChartMorphism freeProjectivizationToBase
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The chart ring of `z_i` is the polynomial ring in `n` variables (accepted coordinate swap and
dehomogenization). -/
def coordinateChartAffineEquiv (i : Fin (n + 1)) :
    coordinateChartRing R n i ≃+* affineRing R n :=
  (firstChartEquivCoordinateChart R n i).symm.trans (coordinateRingEquiv R n)

/-- The coordinate charts as an open cover with universe-lifted index. -/
def coordinateChartCover : Scheme.OpenCover.{u} (freeProjectivization R n) where
  J := ULift.{u} (Fin (n + 1))
  obj i := Spec (CommRingCat.of (coordinateChartRing R n i.down))
  map i := coordinateChartMorphism R n i.down
  f x := ⟨(standardAffineCover R n).f x⟩
  covers x := (standardAffineCover R n).covers x

@[simp] theorem coordinateChartCover_map (i : ULift.{u} (Fin (n + 1))) :
    (coordinateChartCover R n).map i = coordinateChartMorphism R n i.down := rfl

/-- The coordinate ring of the overlap `D(z_i) ∩ D(z_j)`. -/
abbrev coordinateOverlapRing (i j : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading R n)
    ((MvPolynomial.X i : homogeneousRing R n) * MvPolynomial.X j)

theorem coordinate_mul_mem (i j : Fin (n + 1)) :
    (MvPolynomial.X i : homogeneousRing R n) * MvPolynomial.X j ∈ grading R n (1 + 1) :=
  SetLike.mul_mem_graded (coordinate_mem R n i) (coordinate_mem R n j)

/-- The `Proj` chart of the product `z_i z_j`. -/
def coordinateOverlapMorphism (i j : Fin (n + 1)) :
    Spec (CommRingCat.of (coordinateOverlapRing R n i j)) ⟶ freeProjectivization R n :=
  Proj.awayι (grading R n) _ (coordinate_mul_mem R n i j) (by decide)

/-- Restriction from the chart of `z_i` to the overlap with the chart of `z_j`. -/
def toOverlapLeft (i j : Fin (n + 1)) :
    coordinateChartRing R n i →+* coordinateOverlapRing R n i j :=
  HomogeneousLocalization.awayMap (grading R n) (coordinate_mem R n j) rfl

/-- Restriction from the chart of `z_j` to the overlap with the chart of `z_i`. -/
def toOverlapRight (i j : Fin (n + 1)) :
    coordinateChartRing R n j →+* coordinateOverlapRing R n i j :=
  HomogeneousLocalization.awayMap (grading R n) (coordinate_mem R n i) (mul_comm _ _)

/-- The overlap of two coordinate charts is the chart of the product coordinate. -/
def coordinateOverlapIso (i j : Fin (n + 1)) :
    pullback (coordinateChartMorphism R n i) (coordinateChartMorphism R n j) ≅
      Spec (CommRingCat.of (coordinateOverlapRing R n i j)) :=
  Proj.pullbackAwayιIso (grading R n) (coordinate_mem R n i) Nat.one_pos
    (coordinate_mem R n j) Nat.one_pos rfl

@[reassoc]
theorem coordinateOverlapIso_inv_fst (i j : Fin (n + 1)) :
    (coordinateOverlapIso R n i j).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (toOverlapLeft R n i j)) :=
  Proj.pullbackAwayιIso_inv_fst (grading R n) (coordinate_mem R n i) Nat.one_pos
    (coordinate_mem R n j) Nat.one_pos rfl

@[reassoc]
theorem coordinateOverlapIso_inv_snd (i j : Fin (n + 1)) :
    (coordinateOverlapIso R n i j).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (toOverlapRight R n i j)) :=
  Proj.pullbackAwayιIso_inv_snd (grading R n) (coordinate_mem R n i) Nat.one_pos
    (coordinate_mem R n j) Nat.one_pos rfl

/-- The chart of `z_i`, restricted to the overlap, is the chart of `z_i z_j`. -/
@[reassoc]
theorem SpecMap_toOverlapLeft_chart (i j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (toOverlapLeft R n i j)) ≫ coordinateChartMorphism R n i =
      coordinateOverlapMorphism R n i j :=
  Proj.SpecMap_awayMap_awayι (grading R n) (coordinate_mem R n i) Nat.one_pos
    (coordinate_mem R n j) rfl

/-- The chart of `z_j`, restricted to the overlap, is the chart of `z_i z_j`. -/
@[reassoc]
theorem SpecMap_toOverlapRight_chart (i j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (toOverlapRight R n i j)) ≫ coordinateChartMorphism R n j =
      coordinateOverlapMorphism R n i j :=
  Proj.SpecMap_awayMap_awayι (grading R n) (coordinate_mem R n j) Nat.one_pos
    (coordinate_mem R n i) (mul_comm _ _)

/-- The two restrictions to the overlap agree after the chart maps (the pullback square). -/
theorem overlap_condition (i j : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (toOverlapLeft R n i j)) ≫ coordinateChartMorphism R n i =
      Spec.map (CommRingCat.ofHom (toOverlapRight R n i j)) ≫ coordinateChartMorphism R n j := by
  rw [SpecMap_toOverlapLeft_chart, SpecMap_toOverlapRight_chart]

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coordinateChartCover
#print axioms KltDP.Geometry.RelativeProjectiveChart.coordinateOverlapIso
