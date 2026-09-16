import KltDP.Geometry.ModuleCohomologyEuler
import KltDP.Geometry.SurfaceCohomologyVanishing
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Actual global sections from the surface Euler bound

For cohomology vanishing above degree one, the existing alternating finrank
expression is the difference of its two original low-degree dimensions.
Its degree-zero dimension is the dimension of the original global sections,
through the existing base-field-linear H0 comparison. The pinned finite-rank
existence theorem then produces independent original sections.

The section-existence theorems retain finite-dimensionality of the actual
cohomology as an explicit premise. On a normal projective surface the proved
dimension bound supplies vanishing above degree two, so only actual H2
vanishing remains an additional premise. No Riemann--Roch equality, Serre
duality, positive Euler value or effective divisor is assumed implicitly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (M : X.Modules)

/-- The original H0 dimension is the dimension of the original global
sections, with the action induced by the original structure map. -/
theorem cohomologyDimension_zero_eq_finrank_sections :
    letI := baseSectionsModule f M
    cohomologyDimension f M 0 = Module.finrank k (sections M) := by
  letI := baseModule f M 0
  letI := baseSectionsModule f M
  exact (hZeroBaseLinearEquivSections f M).finrank_eq

/-- Actual H0 finiteness transfers to those same global sections. -/
theorem sections_finiteDimensional_of_hZero
    (hfinite : FiniteDimensional k ((baseFunctor f 0).obj M)) :
    letI := baseSectionsModule f M
    FiniteDimensional k (sections M) := by
  letI := baseModule f M 0
  letI := baseSectionsModule f M
  letI : FiniteDimensional k (H M 0) := hfinite
  exact Module.Finite.equiv (hZeroBaseLinearEquivSections f M)

/-- Boundedness alone identifies the existing finrank expression with its
two original terms. Finiteness remains separate in its cohomological uses. -/
theorem eulerCharacteristic_eq_zero_sub_one_of_vanishing
    (hvanish : ∀ i, 1 < i → Subsingleton (H M i)) :
    eulerCharacteristic f M =
      (cohomologyDimension f M 0 : ℤ) - (cohomologyDimension f M 1 : ℤ) := by
  rw [eulerCharacteristic_eq_truncatedEuler f M 1 hvanish]
  simp only [truncatedEuler, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, one_mul, neg_one_mul, zero_add, sub_eq_add_neg]

/-- Nonnegativity of the original H1 dimension bounds the original Euler
expression by the original H0 dimension. -/
theorem eulerCharacteristic_le_dimension_zero_of_vanishing
    (hvanish : ∀ i, 1 < i → Subsingleton (H M i)) :
    eulerCharacteristic f M ≤ (cohomologyDimension f M 0 : ℤ) := by
  rw [eulerCharacteristic_eq_zero_sub_one_of_vanishing f M hvanish]
  exact sub_le_self _ (Int.natCast_nonneg _)

/-- A lower Euler bound produces an actual independent family of original
sections. Both cohomological finiteness and upper vanishing are explicit. -/
theorem exists_linearIndependent_sections_of_le_euler
    (hfinite : ∀ i, FiniteDimensional k ((baseFunctor f i).obj M))
    (hvanish : ∀ i, 1 < i → Subsingleton (H M i))
    (r : ℕ) (hr : (r : ℤ) ≤ eulerCharacteristic f M) :
    letI := baseSectionsModule f M
    ∃ s : Fin r → sections M, LinearIndependent k s := by
  letI := baseSectionsModule f M
  letI : FiniteDimensional k (sections M) :=
    sections_finiteDimensional_of_hZero f M (hfinite 0)
  have h := eulerCharacteristic_le_dimension_zero_of_vanishing f M hvanish
  rw [cohomologyDimension_zero_eq_finrank_sections f M] at h
  apply exists_linearIndependent_of_le_finrank
  omega

end Scheme

section Surface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)
  (M : X.toScheme.Modules)

/-- The existing dimension-two vanishing, together with the supplied
actual H2 vanishing, gives the bound used by section extraction. -/
theorem normalProjectiveSurface_H_subsingleton_above_one
    (h₂ : Subsingleton (H M 2)) (i : ℕ) (hi : 1 < i) : Subsingleton (H M i) := by
  by_cases h : i = 2
  · subst i
    exact h₂
  · exact normalProjectiveSurface_H_subsingleton X M i (by omega)

/-- On an original normal projective surface, an Euler lower bound and H2
vanishing produce independent original global sections over its base field. -/
theorem normalProjectiveSurface_exists_linearIndependent_sections_of_le_euler
    (hfinite : ∀ i, FiniteDimensional k ((baseFunctor X.structureMorphism i).obj M))
    (h₂ : Subsingleton (H M 2)) (r : ℕ)
    (hr : (r : ℤ) ≤ eulerCharacteristic X.structureMorphism M) :
    letI := baseSectionsModule X.structureMorphism M
    ∃ s : Fin r → sections M, LinearIndependent k s :=
  exists_linearIndependent_sections_of_le_euler X.structureMorphism M hfinite
    (normalProjectiveSurface_H_subsingleton_above_one X M h₂) r hr

/-- The positive-Euler specialization returns an actual nonzero section,
not merely positivity of a chosen numerical h0 value. -/
theorem normalProjectiveSurface_exists_nonzero_section_of_euler_pos
    (hfinite : ∀ i, FiniteDimensional k ((baseFunctor X.structureMorphism i).obj M))
    (h₂ : Subsingleton (H M 2))
    (hχ : 0 < eulerCharacteristic X.structureMorphism M) :
    ∃ s : sections M, s ≠ 0 := by
  letI := baseSectionsModule X.structureMorphism M
  obtain ⟨s, hs⟩ := normalProjectiveSurface_exists_linearIndependent_sections_of_le_euler
    X M hfinite h₂ 1 (by omega)
  exact ⟨s 0, LinearIndependent.ne_zero 0 hs⟩

/-- Euler value at least two yields two independent actual sections, the
section-theoretic input needed by later pencil constructions. -/
theorem normalProjectiveSurface_exists_two_independent_sections_of_two_le_euler
    (hfinite : ∀ i, FiniteDimensional k ((baseFunctor X.structureMorphism i).obj M))
    (h₂ : Subsingleton (H M 2))
    (hχ : 2 ≤ eulerCharacteristic X.structureMorphism M) :
    letI := baseSectionsModule X.structureMorphism M
    ∃ s : Fin 2 → sections M, LinearIndependent k s :=
  normalProjectiveSurface_exists_linearIndependent_sections_of_le_euler X M hfinite h₂ 2 hχ

end Surface

end KltDP.Geometry.ModuleCohomology
