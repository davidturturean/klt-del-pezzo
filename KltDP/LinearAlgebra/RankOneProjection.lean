import KltDP.LinearAlgebra.CanonicalCorrection
import KltDP.Lattices.OrthogonalRank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic

/-!
# Projection onto an actual orthogonal line

This module supplies the bilinear algebra in manuscript `lem:projection`
(`source/manuscript.tex`, lines 605–635). The exceptional space is the span
of actual independent vectors `G i`, the ambient dimension is their number
plus one, and the ambient bilinear form is symmetric and nondegenerate.
For an actual vector `L` perpendicular to those vectors, with nonzero
self-pairing, the orthogonal complement is proved to be the line spanned
by `L`, using dimensions and submodule inclusion.

The correction of an arbitrary vector `P` is constructed from the inverse
of the actual negative Gram matrix. Its orthogonality, scalar projection
formula, and square formula are conclusions. No projection identity or
rank-one orthogonal-complement equality is assumed. The negative Gram
matrix is required to be invertible; negative definiteness is unnecessary
for this algebraic calculation.

The final ordered-field specialization gives the manuscript's strict Green
inequality when `P` has square minus one and both `B L L` and `B L P` are
positive. The field may be the rationals or the reals. The geometric
interpretation of the vectors and form, the Picard dimension, exceptional
independence and invertibility, and the positivity hypotheses remain
geometric obligations. The separate canonical-charge identity is not
asserted by this module.
-/

namespace KltDP.LinearAlgebra.RankOneProjection

open Matrix Module
open CanonicalCorrection
open scoped BigOperators

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The exceptional space is the actual span of the supplied vectors. -/
def exceptionalSpan (G : ι → V) : Submodule k V :=
  Submodule.span k (Set.range G)

/-- Orthogonality to the actual span is equivalent to orthogonality to
each supplied vector, in Mathlib's first-argument orientation. -/
theorem mem_orthogonal_exceptionalSpan_iff (B : LinearMap.BilinForm k V)
    (G : ι → V) (x : V) :
    x ∈ B.orthogonal (exceptionalSpan G) ↔ ∀ i, B (G i) x = 0 := by
  constructor
  · intro hx i
    exact hx (G i) (Submodule.subset_span ⟨i, rfl⟩)
  · intro hx
    have hspan : exceptionalSpan G ≤ LinearMap.ker (B.flip x) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hx i
    intro v hv
    exact hspan hv

section Dimension

variable [FiniteDimensional k V]

/-- A nonisotropic vector in the orthogonal complement of a codimension-one
space spans that complement. The equality is derived from dimensions. -/
theorem orthogonal_eq_span_of_codimension_one
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (E : Submodule k V) (hcodim : finrank k V = finrank k E + 1)
    (L : V) (hLE : L ∈ B.orthogonal E) (hLL : B L L ≠ 0) :
    B.orthogonal E = Submodule.span k ({L} : Set V) := by
  have hL : L ≠ 0 := by
    intro hz
    apply hLL
    simp only [hz, B.zero_left]
  have hle : Submodule.span k ({L} : Set V) ≤ B.orthogonal E := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hLE
  have horth : finrank k (B.orthogonal E) = 1 := by
    rw [KltDP.Lattices.OrthogonalRank.finrank_orthogonal B hB E, hcodim]
    omega
  have hdim : finrank k (Submodule.span k ({L} : Set V)) =
      finrank k (B.orthogonal E) := by
    rw [finrank_span_singleton hL, horth]
  exact (Submodule.eq_of_le_of_finrank_eq hle hdim).symm

variable [Fintype ι]

/-- Independence and the actual ambient dimension prove the needed
codimension; it is not encoded as a projection hypothesis. -/
theorem orthogonal_exceptionalSpan_eq_span
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate) (hSymm : B.IsSymm)
    (G : ι → V) (hG : LinearIndependent k G)
    (hdim : finrank k V = Fintype.card ι + 1)
    (L : V) (hLG : ∀ i, B L (G i) = 0) (hLL : B L L ≠ 0) :
    B.orthogonal (exceptionalSpan G) = Submodule.span k ({L} : Set V) := by
  apply orthogonal_eq_span_of_codimension_one B hB (exceptionalSpan G) ?_ L ?_ hLL
  · change finrank k V = finrank k (Submodule.span k (Set.range G)) + 1
    rw [finrank_span_eq_card hG]
    exact hdim
  · apply (mem_orthogonal_exceptionalSpan_iff B G L).mpr
    intro i
    rw [hSymm.eq (G i) L, hLG i]

end Dimension

section Correction

variable [Fintype ι] [DecidableEq ι]

/-- The actual corrected vector, with inverse-matrix coefficients computed
from the pairings of `P` with the exceptional family. -/
noncomputable def projectedClass (B : LinearMap.BilinForm k V) (P : V) (G : ι → V) : V :=
  P + correction G ((negativeGram B G)⁻¹ *ᵥ contactVector B P G)

/-- The inverse row equation proves orthogonality of the constructed vector. -/
theorem projectedClass_mem_orthogonal (B : LinearMap.BilinForm k V)
    (hSymm : B.IsSymm) (P : V) (G : ι → V) (hA : IsUnit (negativeGram B G)) :
    projectedClass B P G ∈ B.orthogonal (exceptionalSpan G) := by
  apply (mem_orthogonal_exceptionalSpan_iff B G _).mpr
  intro i
  have hpair := family_pairing_correction_of_solve B P G
    ((negativeGram B G)⁻¹ *ᵥ contactVector B P G) (inverse_source_solves B P G hA) i
  rw [projectedClass, B.add_right, hpair, hSymm.eq (G i) P]
  simp only [sourceVector, add_neg_cancel]

/-- Pairing with a vector perpendicular to the exceptional family is
unchanged by the actual correction. -/
theorem pairing_projectedClass (B : LinearMap.BilinForm k V)
    (P : V) (G : ι → V) (L : V) (hLG : ∀ i, B L (G i) = 0) :
    B L (projectedClass B P G) = B L P := by
  rw [projectedClass, B.add_right, pairing_correction_right]
  simp [dotProduct, hLG]

/-- Squaring the constructed vector gives its Schur-complement expression
in the actual bilinear space. -/
theorem projectedClass_square (B : LinearMap.BilinForm k V)
    (hSymm : B.IsSymm) (P : V) (G : ι → V) (hA : IsUnit (negativeGram B G)) :
    B (projectedClass B P G) (projectedClass B P G) =
      B P P + dotProduct (contactVector B P G)
        ((negativeGram B G)⁻¹ *ᵥ contactVector B P G) := by
  have h := correctedClass_square_inverse B hSymm P G hA
  simpa only [correctedClass, projectedClass, sourceVector, contactVector,
    B.neg_left, B.neg_right, neg_neg] using h

variable [FiniteDimensional k V]

/-- The scalar projection formula follows from the proved orthogonal line
and the pairing with `L`. -/
theorem projectedClass_eq_smul (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (hSymm : B.IsSymm)
    (P : V) (G : ι → V) (hG : LinearIndependent k G)
    (hdim : finrank k V = Fintype.card ι + 1)
    (hA : IsUnit (negativeGram B G))
    (L : V) (hLG : ∀ i, B L (G i) = 0) (hLL : B L L ≠ 0) :
    projectedClass B P G = (B L P / B L L) • L := by
  have hmem := projectedClass_mem_orthogonal B hSymm P G hA
  rw [orthogonal_exceptionalSpan_eq_span B hB hSymm G hG hdim L hLG hLL] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hLP : B L P = c * B L L := by
    calc
      B L P = B L (projectedClass B P G) := (pairing_projectedClass B P G L hLG).symm
      _ = c * B L L := by rw [← hc, B.smul_right]
  have hc' : c = B L P / B L L := (eq_div_iff hLL).mpr hLP.symm
  rw [← hc, hc']

/-- Equality of the two computations of the actual corrected square. -/
theorem projection_square_identity (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (hSymm : B.IsSymm)
    (P : V) (G : ι → V) (hG : LinearIndependent k G)
    (hdim : finrank k V = Fintype.card ι + 1)
    (hA : IsUnit (negativeGram B G))
    (L : V) (hLG : ∀ i, B L (G i) = 0) (hLL : B L L ≠ 0) :
    B P P + dotProduct (contactVector B P G)
        ((negativeGram B G)⁻¹ *ᵥ contactVector B P G) = (B L P) ^ 2 / B L L := by
  calc
    B P P + dotProduct (contactVector B P G)
        ((negativeGram B G)⁻¹ *ᵥ contactVector B P G) =
        B (projectedClass B P G) (projectedClass B P G) :=
      (projectedClass_square B hSymm P G hA).symm
    _ = (B L P / B L L) ^ 2 * B L L := by
      rw [projectedClass_eq_smul B hB hSymm P G hG hdim hA L hLG hLL]
      simp only [B.smul_left, B.smul_right]
      ring
    _ = (B L P) ^ 2 / B L L := by
      field_simp [hLL]; ring

section Ordered

variable [LinearOrder k] [IsStrictOrderedRing k]

/-- For a vector of square minus one, positive `L` square and positive
degree give both the Green identity and its strict inequality. -/
theorem green_identity_and_gt_one (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (hSymm : B.IsSymm)
    (P : V) (hPP : B P P = -1) (G : ι → V) (hG : LinearIndependent k G)
    (hdim : finrank k V = Fintype.card ι + 1)
    (hA : IsUnit (negativeGram B G))
    (L : V) (hLG : ∀ i, B L (G i) = 0) (hLL : 0 < B L L) (hLP : 0 < B L P) :
    dotProduct (contactVector B P G) ((negativeGram B G)⁻¹ *ᵥ contactVector B P G) =
        1 + (B L P) ^ 2 / B L L ∧
      1 < dotProduct (contactVector B P G) ((negativeGram B G)⁻¹ *ᵥ contactVector B P G) := by
  have h := projection_square_identity B hB hSymm P G hG hdim hA L hLG hLL.ne'
  rw [hPP] at h
  have hpos : 0 < (B L P) ^ 2 / B L L := div_pos (sq_pos_of_pos hLP) hLL
  constructor <;> linarith

end Ordered
end Correction

end KltDP.LinearAlgebra.RankOneProjection
