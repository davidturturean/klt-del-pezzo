/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license; see docs/PROJ_GENERATED_COVER_LICENSE.txt.
Authors: Andrew Yang

The proof of `irrelevant_le_span_of_adjoin_eq_top` is extracted from
Mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f,
AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:97–130,
`Proj.iSup_basicOpen_eq_top'`. It is specialized to the pinned
submodule grading interface. The mathematical statement is unchanged.
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Homogeneous generators give a Proj cover

This bounded upstream proof identifies the necessary irrelevant-ideal
inclusion from actual algebra generation over degree zero. It supplies
both the basic-open cover equality and the input for an affine cover.
-/

noncomputable section

namespace KltDP.ProjGeneratedCover

open AlgebraicGeometry

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- Homogeneous generators as an algebra over degree zero generate an
ideal containing the irrelevant ideal. -/
theorem irrelevant_le_span_of_adjoin_eq_top {ι : Type*} (f : ι → A)
    (hfn : ∀ i, ∃ n, f i ∈ 𝒜 n)
    (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f) := by
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have hx : x ∈ Algebra.adjoin (𝒜 0) (Set.range f) := by
    rw [hf]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hfn i
    rw [GradedRing.projZeroRingHom_apply]
    by_cases hn' : n = 0
    · rw [DirectSum.decompose_of_mem_same 𝒜 (hn' ▸ hn), sub_self]
      exact zero_mem _
    · rw [DirectSum.decompose_of_mem_ne 𝒜 hn hn', sub_zero]
      exact Ideal.subset_span ⟨_, rfl⟩
  | algebraMap r =>
    change (r : A) - GradedRing.projZeroRingHom 𝒜 (r : A) ∈ Ideal.span (Set.range f)
    rw [GradedRing.projZeroRingHom_apply,
      DirectSum.decompose_of_mem_same 𝒜 r.2, sub_self]
    exact zero_mem _
  | add x y _hx _hy hx' hy' =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hx' hy'
  | mul x y _hx _hy hx' hy' =>
    have heq : x * y - GradedRing.projZeroRingHom 𝒜 (x * y) =
        x * (y - GradedRing.projZeroRingHom 𝒜 y) +
          (x - GradedRing.projZeroRingHom 𝒜 x) * GradedRing.projZeroRingHom 𝒜 y := by
      rw [map_mul]
      ring
    rw [heq]
    exact add_mem (Ideal.mul_mem_left _ x hy')
      (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx')

/-- The basic opens of a homogeneous algebra generating family cover
the actual Proj scheme. -/
theorem iSup_basicOpen_eq_top {ι : Type*} (f : ι → A)
    (hfn : ∀ i, ∃ n, f i ∈ 𝒜 n)
    (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    (⨆ i, Proj.basicOpen 𝒜 (f i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top 𝒜 f
    (irrelevant_le_span_of_adjoin_eq_top 𝒜 f hfn hf)

end KltDP.ProjGeneratedCover
