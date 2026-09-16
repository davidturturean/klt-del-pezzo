import KltDP.Geometry.ModuleCohomologyEuler
import KltDP.Geometry.SurfaceCohomologyVanishing
import KltDP.Geometry.FiniteTypeSurfaceRegularity
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finite Euler interpretation in dimension at most one

Properness over the original field gives a Noetherian scheme by the existing
finite-type argument. Grothendieck vanishing then bounds every actual module
sheaf's cohomology by one. The original finsum therefore has just its H0/H1
terms. Finite-dimensionality of those two groups remains explicit; no
proper-cohomology finiteness statement is imported here.

The short-exact Euler identity reuses the existing actual long exact sequence
and bounded Euler theorem. These results require no reducedness, integrality,
nonemptiness or local-freeness assumption. On an empty scheme all the original
cohomology groups vanish, including H0.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The empty scheme has zero actual cohomology in every degree. Its
irreducible-closed-set poset is empty, so its dimension is bottom. -/
theorem scheme_H_subsingleton_of_isEmpty
    (X : Scheme.{u}) [IsEmpty X] (M : X.Modules) (n : ℕ) :
    Subsingleton (H M n) := by
  letI : IsEmpty (IrreducibleCloseds X) := ⟨fun Z => by
    obtain ⟨x, _⟩ := Z.isIrreducible.nonempty
    exact isEmptyElim x⟩
  apply scheme_H_subsingleton_of_dimension_lt X M n
  change Order.krullDim (IrreducibleCloseds X) < (n : WithBot ℕ∞)
  rw [Order.krullDim_eq_bot]
  exact WithBot.bot_lt_coe (n : ℕ∞)

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The finsum Euler expression is zero on the actual empty scheme. -/
theorem eulerCharacteristic_eq_zero_of_isEmpty [IsEmpty X] (M : X.Modules) :
    eulerCharacteristic f M = 0 := by
  have hz : ∀ n, cohomologyDimension f M n = 0 := by
    intro n
    letI := scheme_H_subsingleton_of_isEmpty X M n
    exact cohomologyDimension_eq_zero_of_subsingleton f M n
  simp [eulerCharacteristic, hz]

variable [hproper : IsProper f] (hdim : topologicalKrullDim X ≤ 1)

include hproper hdim

/-- On any proper scheme of dimension at most one, actual cohomology above
one vanishes for every coefficient module, including noncoherent ones. -/
theorem proper_H_subsingleton_of_dimension_le_one
    (M : X.Modules) (n : ℕ) (hn : 1 < n) : Subsingleton (H M n) := by
  letI : IsNoetherian X := isNoetherian_of_finiteType_toSpec f
  apply scheme_H_subsingleton_of_dimension_lt X M n
  exact lt_of_le_of_lt hdim (by exact_mod_cast hn)

/-- The low-degree finiteness contract is equivalent to all-degree
finiteness for the original structure morphism's base-field cohomology. -/
theorem proper_finiteDimensional_iff_of_dimension_le_one (M : X.Modules) :
    (∀ n, FiniteDimensional k ((baseFunctor f n).obj M)) ↔
      FiniteDimensional k ((baseFunctor f 0).obj M) ∧
        FiniteDimensional k ((baseFunctor f 1).obj M) := by
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ n
    rcases n with _ | (_ | n)
    · exact h0
    · exact h1
    · letI := baseModule f M (n + 2)
      letI : Subsingleton ((baseFunctor f (n + 2)).obj M) :=
        proper_H_subsingleton_of_dimension_le_one f hdim M (n + 2) (by omega)
      exact Module.Finite.of_surjective (0 : k →ₗ[k] H M (n + 2))
        (fun y => ⟨0, Subsingleton.elim _ _⟩)

/-- The original totalized Euler expression equals its two actual finrank
terms. Calling these finite cohomological dimensions additionally uses the
preceding explicit finiteness contract. -/
theorem proper_eulerCharacteristic_eq_h0_sub_h1 (M : X.Modules) :
    eulerCharacteristic f M =
      (cohomologyDimension f M 0 : ℤ) - (cohomologyDimension f M 1 : ℤ) := by
  rw [eulerCharacteristic_eq_truncatedEuler f M 1
    (proper_H_subsingleton_of_dimension_le_one f hdim M)]
  simp [truncatedEuler, Finset.sum_range_succ, sub_eq_add_neg]

/-- An actual short exact sequence on the proper scheme satisfies Euler
additivity once its six original H0/H1 groups are finite-dimensional. -/
theorem proper_eulerCharacteristic_additive_of_dimension_le_one
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hfinite₁ : FiniteDimensional k ((baseFunctor f 0).obj S.X₁) ∧
      FiniteDimensional k ((baseFunctor f 1).obj S.X₁))
    (hfinite₂ : FiniteDimensional k ((baseFunctor f 0).obj S.X₂) ∧
      FiniteDimensional k ((baseFunctor f 1).obj S.X₂))
    (hfinite₃ : FiniteDimensional k ((baseFunctor f 0).obj S.X₃) ∧
      FiniteDimensional k ((baseFunctor f 1).obj S.X₃)) :
    eulerCharacteristic f S.X₂ =
      eulerCharacteristic f S.X₁ + eulerCharacteristic f S.X₃ :=
  eulerCharacteristic_additive f S hS 1
    ((proper_finiteDimensional_iff_of_dimension_le_one f hdim S.X₁).mpr hfinite₁)
    ((proper_finiteDimensional_iff_of_dimension_le_one f hdim S.X₂).mpr hfinite₂)
    ((proper_finiteDimensional_iff_of_dimension_le_one f hdim S.X₃).mpr hfinite₃)
    (proper_H_subsingleton_of_dimension_le_one f hdim S.X₁)
    (proper_H_subsingleton_of_dimension_le_one f hdim S.X₂)
    (proper_H_subsingleton_of_dimension_le_one f hdim S.X₃)

end KltDP.Geometry.ModuleCohomology
