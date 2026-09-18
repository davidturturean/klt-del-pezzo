import KltDP.Geometry.ProperInvertibleSectionBasis
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# An exact-length tuple for the complete linear system

A nonzero original top section gives positive H0 dimension. Reindexing the
whole finite basis then produces exactly `dim H0` compatible global sections
in the `Fin (n + 1)` format for projective coordinates, with no extra section.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CompleteLinearSystemSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open ModuleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
  [hproper : IsProper f]

include hproper

/-- A nonzero original global section forces the dimension of actual H0 to be positive. -/
theorem dimension_pos_of_nonzero_top_section (s : L.obj.sections)
    (hs : s.val (op ⊤) ≠ 0) : 0 < dimension f L := by
  letI := baseSectionsModule f L.obj
  letI := topSections_finiteDimensional f L
  rw [dimension_eq_finrank_topSections f L]
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨s.val (op ⊤), hs⟩

/-- Positive H0 dimension is equivalent to an actual nonzero compatible global section. -/
theorem dimension_pos_iff_exists_nonzero_top_section :
    0 < dimension f L ↔ ∃ s : L.obj.sections, s.val (op ⊤) ≠ 0 := by
  letI := baseSectionsModule f L.obj
  letI := topSections_finiteDimensional f L
  constructor
  · intro hpos
    rw [dimension_eq_finrank_topSections f L] at hpos
    obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    refine ⟨(schemeModuleSectionsEquivTop L.obj).symm v, ?_⟩
    change (schemeModuleSectionsEquivTop L.obj)
      ((schemeModuleSectionsEquivTop L.obj).symm v) ≠ 0
    simpa only [Equiv.apply_symm_apply] using hv
  · rintro ⟨s, hs⟩
    exact dimension_pos_of_nonzero_top_section f L s hs

/-- The projective-coordinate tuple has exactly the dimension of the entire original H0. -/
theorem positiveTuple_length (hpos : 0 < dimension f L) :
    (dimension f L - 1) + 1 = dimension f L :=
  Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)

/-- The entire original top-section basis, reindexed into positive-length tuple format. -/
def positiveTopSectionBasis (hpos : 0 < dimension f L) :
    letI := baseSectionsModule f L.obj
    Basis (Fin ((dimension f L - 1) + 1)) k (ModuleCohomology.sections L.obj) := by
  letI := baseSectionsModule f L.obj
  exact (topSectionBasis f L).reindex (finCongr (positiveTuple_length f L hpos).symm)

/-- The compatible original global sections of that exact-length whole basis. -/
def positiveBasisSections (hpos : 0 < dimension f L) :
    Fin ((dimension f L - 1) + 1) → L.obj.sections := by
  letI := baseSectionsModule f L.obj
  exact fun i =>
    (schemeModuleSectionsEquivTop L.obj).symm (positiveTopSectionBasis f L hpos i)

/-- Each coordinate is the actual compatible family of its original basis vector. -/
theorem positiveBasisSections_top (hpos : 0 < dimension f L)
    (i : Fin ((dimension f L - 1) + 1)) :
    letI := baseSectionsModule f L.obj
    (positiveBasisSections f L hpos i).val (op ⊤) = positiveTopSectionBasis f L hpos i := by
  letI := baseSectionsModule f L.obj
  exact (schemeModuleSectionsEquivTop L.obj).apply_symm_apply
    (positiveTopSectionBasis f L hpos i)

/-- Every chosen coordinate has nonzero original top value. -/
theorem positiveBasisSections_top_ne_zero (hpos : 0 < dimension f L)
    (i : Fin ((dimension f L - 1) + 1)) :
    (positiveBasisSections f L hpos i).val (op ⊤) ≠ 0 := by
  letI := baseSectionsModule f L.obj
  rw [positiveBasisSections_top f L hpos i]
  exact (positiveTopSectionBasis f L hpos).ne_zero i

/-- The tuple's original top values are linearly independent over the original base field. -/
theorem positiveBasisSections_linearIndependent (hpos : 0 < dimension f L) :
    letI := baseSectionsModule f L.obj
    LinearIndependent (M := ModuleCohomology.sections L.obj) k (fun i =>
      ((positiveBasisSections f L hpos i).val (op ⊤) : ModuleCohomology.sections L.obj)) := by
  letI := baseSectionsModule f L.obj
  simpa only [positiveBasisSections_top] using (positiveTopSectionBasis f L hpos).linearIndependent

/-- The tuple spans all original global sections, so it is the complete linear system. -/
theorem positiveBasisSections_span (hpos : 0 < dimension f L) :
    letI := baseSectionsModule f L.obj
    Submodule.span (M := ModuleCohomology.sections L.obj) k
      (Set.range (fun i =>
        ((positiveBasisSections f L hpos i).val (op ⊤) : ModuleCohomology.sections L.obj))) = ⊤ := by
  letI := baseSectionsModule f L.obj
  simpa only [positiveBasisSections_top] using (positiveTopSectionBasis f L hpos).span_eq

/-- Every original top section has its exact basis expansion in the chosen tuple. -/
theorem positiveBasisSections_sum_repr (hpos : 0 < dimension f L)
    (v : ModuleCohomology.sections L.obj) :
    letI := baseSectionsModule f L.obj
    ∑ i, (let vi : ModuleCohomology.sections L.obj :=
      (positiveBasisSections f L hpos i).val (op ⊤);
      (positiveTopSectionBasis f L hpos).repr v i • vi) = v := by
  letI := baseSectionsModule f L.obj
  simpa only [positiveBasisSections_top] using (positiveTopSectionBasis f L hpos).sum_repr v

end KltDP.Geometry.CompleteLinearSystemSections
