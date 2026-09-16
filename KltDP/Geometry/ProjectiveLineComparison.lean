/-
Portions adapted from PicardAlbanese Curve/P1Charts.lean.
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license; upstream commit and adapted scope are
recorded in audit/literature_candidates/node_cover_inputs/projective_line_comparison.json.
-/
import KltDP.Geometry.ProjectiveSpaceNormal
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The actual projective line and its reciprocal standard charts

The project's dimension-one Proj is the literal standard-graded Proj used by
the reviewed external P1 definition. The structure morphisms agree because
their maps on degree-zero constants agree. No external module is imported.

The standard chart immersions, their actual pullback, and both coordinate
restrictions are retained. The coordinates are the actual homogeneous
fractions X1/X0 and X0/X1, whose restrictions multiply to one.

The elementary localization normalization in `overlap_coordinates_mul` also
occurs in the Apache-2.0 PicardAlbanese source at commit
9223d85c786394721963a9d642b08d066b72a594, Curve/P1Charts.lean:136-142.
Only pinned Mathlib and existing project proofs are used here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization

universe u

namespace KltDP.Geometry.ProjectiveLineComparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 2) k
abbrev homogeneousRing := MvPolynomial (Fin 2) k

/-- This is the same scheme expression used by the external P1 definition. -/
def projIso : projectiveSpace k 1 ≅ Proj (grading k) := Iso.refl _

/-- Explicit degree-zero constants agree with the canonical algebra map. -/
theorem constants_eq_algebraMap :
    projectiveSpaceConstants k 1 = algebraMap k (grading k 0) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  rfl

/-- The original structure morphism agrees with the canonical Proj convention. -/
theorem structureMap_eq :
    projectiveSpaceToSpec k 1 =
      Proj.toSpecZero (grading k) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (grading k 0))) := by
  unfold projectiveSpaceToSpec
  rw [constants_eq_algebraMap]

theorem projIso_hom_structureMap :
    (projIso k).hom ≫ (Proj.toSpecZero (grading k) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (grading k 0)))) =
        projectiveSpaceToSpec k 1 := by
  simpa only [projIso, Iso.refl_hom, Category.id_comp] using (structureMap_eq k).symm

/-- The two actual homogeneous coordinate charts. -/
def chartOpen (i : Fin 2) : (projectiveSpace k 1).Opens :=
  Proj.basicOpen (grading k) (MvPolynomial.X i)

theorem chartOpen_sup : chartOpen k 0 ⊔ chartOpen k 1 = ⊤ := by
  apply le_antisymm le_top
  calc
    ⊤ = ⨆ i : Fin 2, chartOpen k i :=
      (ProjectiveChart.iSup_coordinateStandardOpen k 1).symm
    _ ≤ chartOpen k 0 ⊔ chartOpen k 1 := by
      apply iSup_le
      intro i
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right

theorem chartOpen_inf :
    chartOpen k 0 ⊓ chartOpen k 1 =
      Proj.basicOpen (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1) :=
  (Proj.basicOpen_mul (grading k) (MvPolynomial.X 0) (MvPolynomial.X 1)).symm

abbrev chartRing (i : Fin 2) :=
  HomogeneousLocalization.Away (grading k) (MvPolynomial.X i)

private theorem coordinate_homogeneous (i : Fin 2) :
    (MvPolynomial.X i : homogeneousRing k) ∈ grading k 1 :=
  MvPolynomial.isHomogeneous_X k i

/-- The actual Proj immersion of a homogeneous localization chart. -/
def chartImmersion (i : Fin 2) : Spec (.of (chartRing k i)) ⟶ projectiveSpace k 1 :=
  Proj.awayι (grading k) (MvPolynomial.X i) (coordinate_homogeneous k i) (by decide)

instance (i : Fin 2) : IsOpenImmersion (chartImmersion k i) := by
  unfold chartImmersion
  infer_instance

theorem chartImmersion_opensRange (i : Fin 2) :
    (chartImmersion k i).opensRange = chartOpen k i :=
  Proj.opensRange_awayι (grading k) (MvPolynomial.X i)
    (coordinate_homogeneous k i) (by decide)

/-- The original scalar map on an actual homogeneous chart. -/
def chartConstants (i : Fin 2) : k →+* chartRing k i :=
  (HomogeneousLocalization.fromZeroRingHom (grading k)
    (Submonoid.powers (MvPolynomial.X i))).comp (projectiveSpaceConstants k 1)

theorem chartImmersion_structureMap (i : Fin 2) :
    chartImmersion k i ≫ projectiveSpaceToSpec k 1 =
      Spec.map (CommRingCat.ofHom (chartConstants k i)) := by
  change Proj.awayι (grading k) (MvPolynomial.X i) (coordinate_homogeneous k i)
      (by decide) ≫ (Proj.toSpecZero (grading k) ≫
        Spec.map (CommRingCat.ofHom (projectiveSpaceConstants k 1))) = _
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

theorem chartOpen_isAffineOpen (i : Fin 2) : IsAffineOpen (chartOpen k i) :=
  Proj.isAffineOpen_basicOpen (grading k) (MvPolynomial.X i)
    (coordinate_homogeneous k i) (by decide)

/-- The existing standard affine cover, with these same original chart maps. -/
def affineCover : (projectiveSpace k 1).AffineOpenCover :=
  ProjectiveChart.standardAffineCover k 1

theorem affineCover_map (i : Fin 2) : (affineCover k).map i = chartImmersion k i := rfl

abbrev overlapRing := HomogeneousLocalization.Away (grading k)
  ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)

/-- Actual coefficient restriction from the chart X0 != 0 to the intersection. -/
def toOverlapLeft : chartRing k 0 →+* overlapRing k :=
  HomogeneousLocalization.awayMap (grading k) (coordinate_homogeneous k 1) rfl

/-- Actual coefficient restriction from the chart X1 != 0 to the intersection. -/
def toOverlapRight : chartRing k 1 →+* overlapRing k :=
  HomogeneousLocalization.awayMap (grading k) (coordinate_homogeneous k 0)
    (mul_comm (MvPolynomial.X 0 : homogeneousRing k) (MvPolynomial.X 1))

/-- The actual intersection of chart immersions is the product-coordinate localization. -/
def overlapPullbackIso :
    pullback (chartImmersion k 0) (chartImmersion k 1) ≅ Spec (.of (overlapRing k)) :=
  Proj.pullbackAwayιIso (grading k) (coordinate_homogeneous k 0) (by decide)
    (coordinate_homogeneous k 1) (by decide) rfl

@[simp, reassoc]
theorem overlapPullbackIso_hom_left :
    (overlapPullbackIso k).hom ≫ Spec.map (CommRingCat.ofHom (toOverlapLeft k)) =
      pullback.fst (chartImmersion k 0) (chartImmersion k 1) :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left (grading k)
    (coordinate_homogeneous k 0) (by decide) (coordinate_homogeneous k 1) (by decide) rfl

@[simp, reassoc]
theorem overlapPullbackIso_hom_right :
    (overlapPullbackIso k).hom ≫ Spec.map (CommRingCat.ofHom (toOverlapRight k)) =
      pullback.snd (chartImmersion k 0) (chartImmersion k 1) :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right (grading k)
    (coordinate_homogeneous k 0) (by decide) (coordinate_homogeneous k 1) (by decide) rfl

/-- On chart i this is the actual homogeneous fraction Xj/Xi. -/
def coordinate (i j : Fin 2) : chartRing k i :=
  HomogeneousLocalization.Away.mk (grading k) (coordinate_homogeneous k i) 1
    (MvPolynomial.X j) (by simpa only [one_smul] using coordinate_homogeneous k j)

theorem coordinate_zero_one_eq_ratio :
    coordinate k 0 1 = ProjectiveChart.ratio k 1 (0 : Fin 1) := rfl

/-- The two actual restricted coordinates are multiplicative inverses. -/
theorem overlap_coordinates_mul :
    toOverlapLeft k (coordinate k 0 1) * toOverlapRight k (coordinate k 1 0) = 1 := by
  rw [toOverlapLeft, toOverlapRight, coordinate, coordinate,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_one, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

/-- The actual overlap coordinate, bundled with the proved reciprocal. -/
def overlapUnit : (overlapRing k)ˣ where
  val := toOverlapLeft k (coordinate k 0 1)
  inv := toOverlapRight k (coordinate k 1 0)
  val_inv := overlap_coordinates_mul k
  inv_val := by rw [mul_comm]; exact overlap_coordinates_mul k

@[simp] theorem overlapUnit_val :
    (overlapUnit k : overlapRing k) = toOverlapLeft k (coordinate k 0 1) := rfl

@[simp] theorem overlapUnit_inv_val :
    (((overlapUnit k)⁻¹ : (overlapRing k)ˣ) : overlapRing k) =
      toOverlapRight k (coordinate k 1 0) := rfl

/-- The pinned one-variable renaming, with no new polynomial foundation. -/
def oneVariablePolynomialEquiv : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
  (MvPolynomial.renameEquiv k
    (Equiv.equivPUnit (Fin 1) : Fin 1 ≃ PUnit.{1})).trans (MvPolynomial.pUnitAlgEquiv k)

@[simp] theorem oneVariablePolynomialEquiv_X :
    oneVariablePolynomialEquiv k (MvPolynomial.X (0 : Fin 1)) = Polynomial.X := by
  simp [oneVariablePolynomialEquiv, MvPolynomial.pUnitAlgEquiv]

/-- The first actual homogeneous chart is the ordinary polynomial affine line. -/
def firstChartPolynomialEquiv : chartRing k 0 ≃+* Polynomial k :=
  (ProjectiveChart.coordinateRingEquiv k 1).trans (oneVariablePolynomialEquiv k).toRingEquiv

@[simp] theorem firstChartPolynomialEquiv_coordinate :
    firstChartPolynomialEquiv k (coordinate k 0 1) = Polynomial.X := by
  change oneVariablePolynomialEquiv k
    (ProjectiveChart.dehomogenize k 1 (ProjectiveChart.ratio k 1 (0 : Fin 1))) = _
  rw [ProjectiveChart.dehomogenize_ratio, oneVariablePolynomialEquiv_X]

@[simp] theorem firstChartPolynomialEquiv_constants (r : k) :
    firstChartPolynomialEquiv k (chartConstants k 0 r) = Polynomial.C r := by
  change oneVariablePolynomialEquiv k
    (ProjectiveChart.coordinateRingEquiv k 1 (ProjectiveChart.constants k 1 r)) = _
  rw [ProjectiveChart.coordinateRingEquiv_constants]
  exact (oneVariablePolynomialEquiv k).commutes r

/-- Swapping the homogeneous variables sends X1/X0 to the actual X0/X1 fraction. -/
theorem swap_first_coordinate :
    ProjectiveChart.firstChartEquivCoordinateChart k 1 (1 : Fin 2)
      (coordinate k 0 1) = coordinate k 1 0 := by
  apply congrArg (HomogeneousLocalization.mk
    (𝒜 := grading k)
    (x := Submonoid.powers (MvPolynomial.X (1 : Fin 2) : homogeneousRing k)))
  apply HomogeneousLocalization.NumDenSameDeg.ext
  · rfl
  · change MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
      (MvPolynomial.X 1 : homogeneousRing k) = MvPolynomial.X 0
    rw [MvPolynomial.rename_X, Equiv.swap_apply_right]
  · change MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
      ((MvPolynomial.X 0 : homogeneousRing k) ^ 1) = MvPolynomial.X 1 ^ 1
    rw [map_pow, MvPolynomial.rename_X, Equiv.swap_apply_left]

theorem swap_first_constants (r : k) :
    ProjectiveChart.firstChartEquivCoordinateChart k 1 (1 : Fin 2)
      (chartConstants k 0 r) = chartConstants k 1 r := by
  apply congrArg (HomogeneousLocalization.mk
    (𝒜 := grading k)
    (x := Submonoid.powers (MvPolynomial.X (1 : Fin 2) : homogeneousRing k)))
  apply HomogeneousLocalization.NumDenSameDeg.ext
  · rfl
  · change MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
      (MvPolynomial.C r : homogeneousRing k) = MvPolynomial.C r
    exact MvPolynomial.rename_C _ r
  · change MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (1 : homogeneousRing k) = 1
    exact map_one _

/-- The second chart uses the reciprocal coordinate X0/X1. -/
def secondChartPolynomialEquiv : chartRing k 1 ≃+* Polynomial k :=
  (ProjectiveChart.firstChartEquivCoordinateChart k 1 (1 : Fin 2)).symm.trans
    (firstChartPolynomialEquiv k)

@[simp] theorem secondChartPolynomialEquiv_coordinate :
    secondChartPolynomialEquiv k (coordinate k 1 0) = Polynomial.X := by
  rw [← swap_first_coordinate]
  change firstChartPolynomialEquiv k
    ((ProjectiveChart.firstChartEquivCoordinateChart k 1 (1 : Fin 2)).symm
      (ProjectiveChart.firstChartEquivCoordinateChart k 1 (1 : Fin 2)
        (coordinate k 0 1))) = _
  rw [RingEquiv.symm_apply_apply, firstChartPolynomialEquiv_coordinate]

@[simp] theorem secondChartPolynomialEquiv_constants (r : k) :
    secondChartPolynomialEquiv k (chartConstants k 1 r) = Polynomial.C r := by
  rw [← swap_first_constants]
  change firstChartPolynomialEquiv k
    ((ProjectiveChart.firstChartEquivCoordinateChart k 1 (1 : Fin 2)).symm
      (ProjectiveChart.firstChartEquivCoordinateChart k 1 (1 : Fin 2)
        (chartConstants k 0 r))) = _
  rw [RingEquiv.symm_apply_apply, firstChartPolynomialEquiv_constants]

/-- The actual polynomial coordinate identification on each of the two charts. -/
def chartPolynomialEquiv (i : Fin 2) : chartRing k i ≃+* Polynomial k :=
  Fin.cases (motive := fun i : Fin 2 => chartRing k i ≃+* Polynomial k)
    (firstChartPolynomialEquiv k)
    (Fin.cases (motive := fun j : Fin 1 => chartRing k j.succ ≃+* Polynomial k)
      (secondChartPolynomialEquiv k) (fun j => Fin.elim0 j)) i

@[simp] theorem chartPolynomialEquiv_constants (i : Fin 2) (r : k) :
    chartPolynomialEquiv k i (chartConstants k i r) = Polynomial.C r := by
  fin_cases i
  · simpa only [chartPolynomialEquiv, Fin.cases_zero, Fin.cases_succ] using
      firstChartPolynomialEquiv_constants k r
  · simpa only [chartPolynomialEquiv, Fin.cases_zero, Fin.cases_succ] using
      secondChartPolynomialEquiv_constants k r

/-- Applying the contravariant Spec functor to the actual coordinate equivalence. -/
def chartPolynomialIso (i : Fin 2) :
    Spec (.of (chartRing k i)) ≅ Spec (.of (Polynomial k)) :=
  Scheme.Spec.mapIso (chartPolynomialEquiv k i).symm.toCommRingCatIso.op

/-- The polynomial affine-line charts as actual morphisms into the original Proj. -/
def polynomialChartMap (i : Fin 2) : Spec (.of (Polynomial k)) ⟶ projectiveSpace k 1 :=
  (chartPolynomialIso k i).inv ≫ chartImmersion k i

instance (i : Fin 2) : IsOpenImmersion (polynomialChartMap k i) := by
  unfold polynomialChartMap
  infer_instance

theorem polynomialChartMap_opensRange (i : Fin 2) :
    (polynomialChartMap k i).opensRange = chartOpen k i :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chartImmersion_opensRange k i)

/-- Both polynomial affine-line charts retain the original morphism to Spec k. -/
theorem polynomialChartMap_structureMap (i : Fin 2) :
    polynomialChartMap k i ≫ projectiveSpaceToSpec k 1 =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  rw [polynomialChartMap, Category.assoc, chartImmersion_structureMap]
  change Spec.map (CommRingCat.ofHom (chartPolynomialEquiv k i).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (chartConstants k i)) = _
  rw [← Spec.map_comp]
  have h : (chartPolynomialEquiv k i).toRingHom.comp (chartConstants k i) =
      (Polynomial.C : k →+* Polynomial k) := by
    apply RingHom.ext
    exact chartPolynomialEquiv_constants k i
  exact congrArg (fun t : k →+* Polynomial k => Spec.map (CommRingCat.ofHom t)) h

/-- A proved actual two-chart affine cover by spectra of ordinary polynomial rings. -/
def polynomialAffineCover : (projectiveSpace k 1).AffineOpenCover where
  J := Fin 2
  obj _ := CommRingCat.of (Polynomial k)
  map := polynomialChartMap k
  f := (affineCover k).f
  covers x := by
    obtain ⟨z, hz⟩ := (affineCover k).covers x
    refine ⟨(chartPolynomialIso k ((affineCover k).f x)).hom.base z, ?_⟩
    change (polynomialChartMap k ((affineCover k).f x)).base
      ((chartPolynomialIso k ((affineCover k).f x)).hom.base z) = x
    rw [← Scheme.comp_base_apply, polynomialChartMap, Iso.hom_inv_id_assoc]
    exact hz

private def overlapChartAlgebra : Algebra (chartRing k 0) (overlapRing k) :=
  (toOverlapLeft k).toAlgebra

private theorem overlap_isLocalization :
    letI := overlapChartAlgebra k
    IsLocalization.Away (coordinate k 0 1) (overlapRing k) := by
  letI := overlapChartAlgebra k
  have h := HomogeneousLocalization.Away.isLocalization_mul
    (coordinate_homogeneous k 0) (coordinate_homogeneous k 1) rfl (by decide)
  have he : HomogeneousLocalization.Away.isLocalizationElem
      (coordinate_homogeneous k 0) (coordinate_homogeneous k 1) = coordinate k 0 1 := by
    unfold HomogeneousLocalization.Away.isLocalizationElem coordinate
    congr 1
    exact pow_one _
  rw [← he]
  exact h

/-- The actual overlap ring is the Laurent polynomial ring, via the first coordinate. -/
def overlapLaurentEquiv : overlapRing k ≃+* LaurentPolynomial k := by
  letI := overlapChartAlgebra k
  letI := overlap_isLocalization k
  exact IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (coordinate k 0 1))
    (T := Submonoid.powers (Polynomial.X : Polynomial k))
    (overlapRing k) (LaurentPolynomial k) (firstChartPolynomialEquiv k)
    (by rw [Submonoid.map_powers]
        exact congrArg _ (firstChartPolynomialEquiv_coordinate k))

/-- The entire left restriction is the usual polynomial-to-Laurent homomorphism. -/
theorem overlapLaurentEquiv_left (z : chartRing k 0) :
    overlapLaurentEquiv k (toOverlapLeft k z) =
      Polynomial.toLaurent (firstChartPolynomialEquiv k z) := by
  letI := overlapChartAlgebra k
  letI := overlap_isLocalization k
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

@[simp] theorem overlapLaurentEquiv_left_coordinate :
    overlapLaurentEquiv k (toOverlapLeft k (coordinate k 0 1)) =
      LaurentPolynomial.T 1 := by
  rw [overlapLaurentEquiv_left, firstChartPolynomialEquiv_coordinate, Polynomial.toLaurent_X]

/-- The right coordinate restricts to the inverse Laurent variable. -/
@[simp] theorem overlapLaurentEquiv_right_coordinate :
    overlapLaurentEquiv k (toOverlapRight k (coordinate k 1 0)) =
      LaurentPolynomial.T (-1) := by
  have h := congrArg (overlapLaurentEquiv k) (overlap_coordinates_mul k)
  rw [map_mul, overlapLaurentEquiv_left_coordinate, map_one] at h
  calc
    overlapLaurentEquiv k (toOverlapRight k (coordinate k 1 0)) =
        (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) *
          overlapLaurentEquiv k (toOverlapRight k (coordinate k 1 0)) := by
      rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, one_mul]
    _ = LaurentPolynomial.T (-1) := by rw [mul_assoc, h, mul_one]

/-- This is an isomorphism of the actual chart intersection with the affine torus. -/
def overlapSpecLaurentIso :
    pullback (chartImmersion k 0) (chartImmersion k 1) ≅
      Spec (.of (LaurentPolynomial k)) :=
  overlapPullbackIso k ≪≫
    Scheme.Spec.mapIso (overlapLaurentEquiv k).symm.toCommRingCatIso.op

end KltDP.Geometry.ProjectiveLineComparison
