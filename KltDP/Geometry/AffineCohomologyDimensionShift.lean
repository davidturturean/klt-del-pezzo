/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Adapted from Vilin97/MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SchemeModuleCohomologyDimensionShift.lean:39-91 and
SchemeModuleCohomologyAffineHOne.lean:32-50. The project has already
ported the underlying exact sheaf/cohomology sequences; those are reused.
-/
import KltDP.Geometry.AffineCohomologyCover
import KltDP.Geometry.ModuleCohomologyExact

/-!
# The exact-sequence step for affine vanishing

The ambient cover map is injective on H1 by existing quasicoherent H0
surjectivity, and on H(n+1) when Hn of its actual cokernel vanishes.
The local-killing and degree induction that discharge these intermediate
conditions belong to the subsequent port. Source draft; VM checks pending.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.AffineCohomologyPort

open ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Previous-degree surjectivity makes the next-degree map injective. -/
theorem cohomology_succ_map_injective_of_previous_surjective
    {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    (hsurjective : Function.Surjective ((zariskiFunctor X n).map S.g)) :
    Function.Injective ((zariskiFunctor X (n + 1)).map S.f) := by
  have hSsheaf := KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx⟩ := CategoryTheory.Sheaf.H.longSequence_exact₁
    hSsheaf n (n + 1) rfl c hc
  obtain ⟨y, hy⟩ := hsurjective x
  rw [← hx, ← hy]
  exact CategoryTheory.Sheaf.H.longSequence_comp_zero₃ hSsheaf n (n + 1) rfl y

/-- Vanishing of the actual cokernel cohomology gives the same injectivity. -/
theorem cohomology_succ_map_injective_of_cokernel_subsingleton
    {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (H S.X₃ n)] :
    Function.Injective ((zariskiFunctor X (n + 1)).map S.f) := by
  apply cohomology_succ_map_injective_of_previous_surjective hS n
  intro x
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The original affine-cover map is injective in H1, without a vanishing premise. -/
theorem toAffineCoverModule_HOne_injective {R : Type u} [CommRing R]
    {I : Type u} [Finite I] (M : (Spec (.of R)).Modules) [M.IsQuasicoherent]
    (U : I → (Spec (.of R)).Opens) (hU : IsOpenCover U) [∀ i, IsAffine (U i)] :
    Function.Injective ((zariskiFunctor (Spec (.of R)) 1).map (toAffineCoverModule M U)) := by
  letI := affineCoverModule_isQuasicoherent M U
  exact cohomology_succ_map_injective_of_previous_surjective
    (affineCoverCokernel_shortExact M U hU) 0
    (AffineModuleTilde.hZero_surjective_cokernel_π (toAffineCoverModule M U))

/-- The actual cover-cokernel sequence supplies the induction step. -/
theorem toAffineCoverModule_H_succ_injective_of_cokernel_subsingleton
    {X : Scheme.{u}} {I : Type u} (M : X.Modules) (U : I → X.Opens)
    (hU : IsOpenCover U) (n : ℕ) [Subsingleton (H (cokernel (toAffineCoverModule M U)) n)] :
    Function.Injective ((zariskiFunctor X (n + 1)).map (toAffineCoverModule M U)) :=
  cohomology_succ_map_injective_of_cokernel_subsingleton
    (affineCoverCokernel_shortExact M U hU) n

end KltDP.Geometry.AffineCohomologyPort
