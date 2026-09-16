/-
Portions adapted from PicardAlbanese Curve/P1.lean and Curve/P1Charts.lean.
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license; upstream commit and adapted scope are
recorded in audit/literature_candidates/node_cover_inputs/projective_line_sections.json.
-/
import KltDP.Geometry.ProjectiveLineComparison
import Lean.Elab.Tactic.Omega

/-!
# Sections and restriction maps on the standard projective-line cover

The two chart section rings are polynomial rings, and the intersection section
ring is the Laurent polynomial ring. These equivalences carry the actual
structure-sheaf restrictions to substitution at T and T⁻¹. In particular, the
additive difference of the two restrictions is surjective.

This is a statement about sections on the actual opens of `projectiveSpace k 1`.
No comparison with sheaf cohomology, Picard groups, or divisor degrees is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

namespace KltDP.Geometry.ProjectiveLineSections

open ProjectiveLineComparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

private theorem coordinate_homogeneous (i : Fin 2) :
    (MvPolynomial.X i : homogeneousRing k) ∈ grading k 1 :=
  MvPolynomial.isHomogeneous_X k i

private theorem product_homogeneous :
    ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1) ∈ grading k 2 :=
  SetLike.mul_mem_graded (coordinate_homogeneous k 0) (coordinate_homogeneous k 1)

/-- The intersection as an actual Proj basic open. -/
def overlapOpen : (projectiveSpace k 1).Opens :=
  Proj.basicOpen (grading k)
    ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)

theorem overlapOpen_eq_inf : overlapOpen k = chartOpen k 0 ⊓ chartOpen k 1 :=
  (chartOpen_inf k).symm

theorem overlapOpen_le_left : overlapOpen k ≤ chartOpen k 0 :=
  Proj.basicOpen_mono (grading k) _ _ ⟨MvPolynomial.X 1, rfl⟩

theorem overlapOpen_le_right : overlapOpen k ≤ chartOpen k 1 :=
  Proj.basicOpen_mono (grading k) _ _
    ⟨MvPolynomial.X 0, mul_comm (MvPolynomial.X 0 : homogeneousRing k) (MvPolynomial.X 1)⟩

theorem overlapOpen_isAffineOpen : IsAffineOpen (overlapOpen k) :=
  Proj.isAffineOpen_basicOpen (grading k) _ (product_homogeneous k) (by decide)

/-- Both coefficient restrictions carry a scalar to the same overlap section. -/
theorem toOverlapRight_constants (a : k) :
    toOverlapRight k (chartConstants k 1 a) =
      toOverlapLeft k (chartConstants k 0 a) := by
  simp only [toOverlapRight, toOverlapLeft, chartConstants, RingHom.comp_apply,
    HomogeneousLocalization.awayMap_fromZeroRingHom]

/-- The entire right coefficient restriction, including its scalar map. -/
theorem overlapLaurentEquiv_right (z : chartRing k 1) :
    overlapLaurentEquiv k (toOverlapRight k z) =
      Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k)
        (secondChartPolynomialEquiv k z) := by
  have h : (overlapLaurentEquiv k).toRingHom.comp
      ((toOverlapRight k).comp (secondChartPolynomialEquiv k).symm.toRingHom) =
        (Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change overlapLaurentEquiv k
        (toOverlapRight k ((secondChartPolynomialEquiv k).symm (Polynomial.C a))) =
          Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k) (Polynomial.C a)
      calc
        _ = LaurentPolynomial.C a := by
          rw [← secondChartPolynomialEquiv_constants k a, RingEquiv.symm_apply_apply,
            toOverlapRight_constants, overlapLaurentEquiv_left,
            firstChartPolynomialEquiv_constants, Polynomial.toLaurent_C]
        _ = _ := by
          rw [Polynomial.aeval_C, LaurentPolynomial.C_eq_algebraMap]
    · change overlapLaurentEquiv k
        (toOverlapRight k ((secondChartPolynomialEquiv k).symm Polynomial.X)) =
          Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k) Polynomial.X
      calc
        _ = LaurentPolynomial.T (-1) := by
          rw [← secondChartPolynomialEquiv_coordinate k, RingEquiv.symm_apply_apply,
            overlapLaurentEquiv_right_coordinate]
        _ = _ := (Polynomial.aeval_X (LaurentPolynomial.T (-1) : LaurentPolynomial k)).symm
  have hz := RingHom.congr_fun h (secondChartPolynomialEquiv k z)
  change overlapLaurentEquiv k
    (toOverlapRight k ((secondChartPolynomialEquiv k).symm (secondChartPolynomialEquiv k z))) =
      Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k)
        (secondChartPolynomialEquiv k z) at hz
  simpa only [RingEquiv.symm_apply_apply] using hz

/-- Polynomial coordinates on sections of the first actual chart. -/
def leftSectionsEquiv : Γ(projectiveSpace k 1, chartOpen k 0) ≃+* Polynomial k :=
  (Proj.basicOpenIsoAway (grading k) (MvPolynomial.X 0)
    (coordinate_homogeneous k 0) (by decide)).commRingCatIsoToRingEquiv.symm.trans
      (firstChartPolynomialEquiv k)

/-- Polynomial coordinates on sections of the second actual chart. -/
def rightSectionsEquiv : Γ(projectiveSpace k 1, chartOpen k 1) ≃+* Polynomial k :=
  (Proj.basicOpenIsoAway (grading k) (MvPolynomial.X 1)
    (coordinate_homogeneous k 1) (by decide)).commRingCatIsoToRingEquiv.symm.trans
      (secondChartPolynomialEquiv k)

/-- Laurent coordinates on sections of the actual intersection. -/
def overlapSectionsEquiv : Γ(projectiveSpace k 1, overlapOpen k) ≃+* LaurentPolynomial k :=
  (Proj.basicOpenIsoAway (grading k)
    ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)
    (product_homogeneous k) (by decide)).commRingCatIsoToRingEquiv.symm.trans
      (overlapLaurentEquiv k)

private theorem iso_symm_hom_apply {R S : CommRingCat} (e : R ≅ S) (x : R) :
    e.commRingCatIsoToRingEquiv.symm (e.hom.hom x) = x := by
  exact e.commRingCatIsoToRingEquiv.symm_apply_apply x

theorem leftSectionsEquiv_awayToSection (p : chartRing k 0) :
    leftSectionsEquiv k ((Proj.awayToSection (grading k) (MvPolynomial.X 0)).hom p) =
      firstChartPolynomialEquiv k p := by
  exact congrArg (firstChartPolynomialEquiv k)
    (iso_symm_hom_apply (Proj.basicOpenIsoAway (grading k) (MvPolynomial.X 0)
      (coordinate_homogeneous k 0) (by decide)) p)

theorem rightSectionsEquiv_awayToSection (p : chartRing k 1) :
    rightSectionsEquiv k ((Proj.awayToSection (grading k) (MvPolynomial.X 1)).hom p) =
      secondChartPolynomialEquiv k p := by
  exact congrArg (secondChartPolynomialEquiv k)
    (iso_symm_hom_apply (Proj.basicOpenIsoAway (grading k) (MvPolynomial.X 1)
      (coordinate_homogeneous k 1) (by decide)) p)

theorem overlapSectionsEquiv_awayToSection (p : overlapRing k) :
    overlapSectionsEquiv k
      ((Proj.awayToSection (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)).hom p) =
      overlapLaurentEquiv k p := by
  exact congrArg (overlapLaurentEquiv k)
    (iso_symm_hom_apply (Proj.basicOpenIsoAway (grading k)
      ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)
      (product_homogeneous k) (by decide)) p)

/-- The structure sheaf's canonical left restriction. -/
def restrictLeft : Γ(projectiveSpace k 1, chartOpen k 0) →+*
    Γ(projectiveSpace k 1, overlapOpen k) :=
  ((projectiveSpace k 1).presheaf.map (homOfLE (overlapOpen_le_left k)).op).hom

/-- The structure sheaf's canonical right restriction. -/
def restrictRight : Γ(projectiveSpace k 1, chartOpen k 1) →+*
    Γ(projectiveSpace k 1, overlapOpen k) :=
  ((projectiveSpace k 1).presheaf.map (homOfLE (overlapOpen_le_right k)).op).hom

theorem restrictLeft_awayToSection (p : chartRing k 0) :
    restrictLeft k ((Proj.awayToSection (grading k) (MvPolynomial.X 0)).hom p) =
      (Proj.awayToSection (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)).hom
          (toOverlapLeft k p) := by
  have h := Proj.awayMap_awayToSection (grading k) (coordinate_homogeneous k 1)
    (f := (MvPolynomial.X 0 : homogeneousRing k)) rfl
  have hp := congrArg (fun f : chartRing k 0 →+*
    Γ(projectiveSpace k 1, overlapOpen k) => f p) (congrArg CommRingCat.Hom.hom h)
  exact hp.symm

theorem restrictRight_awayToSection (p : chartRing k 1) :
    restrictRight k ((Proj.awayToSection (grading k) (MvPolynomial.X 1)).hom p) =
      (Proj.awayToSection (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)).hom
          (toOverlapRight k p) := by
  have h := Proj.awayMap_awayToSection (grading k) (coordinate_homogeneous k 0)
    (f := (MvPolynomial.X 1 : homogeneousRing k))
    (mul_comm (MvPolynomial.X 0 : homogeneousRing k) (MvPolynomial.X 1))
  have hp := congrArg (fun f : chartRing k 1 →+*
    Γ(projectiveSpace k 1, overlapOpen k) => f p) (congrArg CommRingCat.Hom.hom h)
  exact hp.symm

private theorem awayToSection_surjective (i : Fin 2) :
    Function.Surjective (Proj.awayToSection (grading k) (MvPolynomial.X i)).hom := by
  intro z
  exact (Proj.basicOpenIsoAway (grading k) (MvPolynomial.X i)
    (coordinate_homogeneous k i) (by decide)).commRingCatIsoToRingEquiv.surjective z

theorem overlapSectionsEquiv_restrictLeft (a : Γ(projectiveSpace k 1, chartOpen k 0)) :
    overlapSectionsEquiv k (restrictLeft k a) =
      Polynomial.toLaurent (leftSectionsEquiv k a) := by
  obtain ⟨p, rfl⟩ := awayToSection_surjective k 0 a
  rw [restrictLeft_awayToSection, overlapSectionsEquiv_awayToSection,
    leftSectionsEquiv_awayToSection, overlapLaurentEquiv_left]

theorem overlapSectionsEquiv_restrictRight (a : Γ(projectiveSpace k 1, chartOpen k 1)) :
    overlapSectionsEquiv k (restrictRight k a) =
      Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k)
        (rightSectionsEquiv k a) := by
  obtain ⟨p, rfl⟩ := awayToSection_surjective k 1 a
  rw [restrictRight_awayToSection, overlapSectionsEquiv_awayToSection,
    rightSectionsEquiv_awayToSection, overlapLaurentEquiv_right]

/-- The elementary Laurent span calculation, adapted from the licensed P1 source. -/
theorem exists_toLaurent_add_aeval (f : LaurentPolynomial k) :
    ∃ p q : Polynomial k, f =
      p.toLaurent + Polynomial.aeval (LaurentPolynomial.T (-1) : LaurentPolynomial k) q := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p₁, q₁, rfl⟩ := hp
    obtain ⟨p₂, q₂, rfl⟩ := hq
    exact ⟨p₁ + p₂, q₁ + q₂, by simp only [map_add]; ring⟩
  | C_mul_T n a =>
    rcases le_or_gt 0 n with hn | hn
    · refine ⟨Polynomial.C a * Polynomial.X ^ n.toNat, 0, ?_⟩
      rw [map_zero, add_zero, Polynomial.toLaurent_C_mul_X_pow, Int.toNat_of_nonneg hn]
    · refine ⟨0, Polynomial.C a * Polynomial.X ^ (-n).toNat, ?_⟩
      rw [map_zero, zero_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        LaurentPolynomial.T_pow, ← LaurentPolynomial.C_eq_algebraMap]
      congr 2
      omega

/-- Every actual overlap section is a sum of restrictions from the two charts. -/
theorem exists_restrictLeft_add_restrictRight
    (s : Γ(projectiveSpace k 1, overlapOpen k)) :
    ∃ (a : Γ(projectiveSpace k 1, chartOpen k 0))
      (b : Γ(projectiveSpace k 1, chartOpen k 1)),
      s = restrictLeft k a + restrictRight k b := by
  obtain ⟨p, q, hpq⟩ := exists_toLaurent_add_aeval k (overlapSectionsEquiv k s)
  refine ⟨(leftSectionsEquiv k).symm p, (rightSectionsEquiv k).symm q, ?_⟩
  apply (overlapSectionsEquiv k).injective
  simpa only [map_add, overlapSectionsEquiv_restrictLeft,
    overlapSectionsEquiv_restrictRight, RingEquiv.apply_symm_apply] using hpq

/-- Surjectivity of the actual two-open additive Čech difference map. -/
theorem restrict_difference_surjective :
    Function.Surjective (fun ab :
      Γ(projectiveSpace k 1, chartOpen k 0) × Γ(projectiveSpace k 1, chartOpen k 1) =>
        restrictLeft k ab.1 - restrictRight k ab.2) := by
  intro s
  obtain ⟨a, b, h⟩ := exists_restrictLeft_add_restrictRight k s
  refine ⟨(a, -b), ?_⟩
  simpa only [map_neg, sub_neg_eq_add] using h.symm

end KltDP.Geometry.ProjectiveLineSections
