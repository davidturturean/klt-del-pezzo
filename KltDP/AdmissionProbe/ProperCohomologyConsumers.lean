import KltDP.Literature.Stacks.ProperCohomologyFinite
import KltDP.Geometry.InvertibleCoherentModule
import KltDP.Geometry.FiniteTypeNoetherian
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
INACTIVE consumers of the exact proposed declaration. This file is usable
only in a root-authorized isolated candidate checkout after the literal
module has been staged there; it is not an active source or an admission.
No global theorem is passed as an extra hypothesis or packaged assumption.
-/

noncomputable section

-- Display-only options: retain explicit types/proofs and avoid normal depth elision.
-- The recipe separately rejects any remaining elision and captures raw Expr JSON.
set_option pp.all true
set_option pp.maxSteps 1000000

open AlgebraicGeometry CategoryTheory KltDP.Geometry
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.AdmissionProbe.ProperCohomologyConsumers

/-- Ordinary transport from the literal derived target to the original Ext H. -/
theorem proper_ext_finite
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (M : X.Modules) [IsCoherentModule M] (n : ℕ) :
    letI := baseRingModule f M n
    Module.Finite A (H M n) := by
  letI := baseRingModule f M n
  letI := baseRingRightDerivedModule f M n
  letI : Module.Finite A (rightDerivedH M n) :=
    KltDP.Literature.Stacks.properCohomology_finite f M n
  exact Module.Finite.equiv (zariskiRightDerivedLinearEquiv f M n).symm

/-- Field specialization uses the existing baseModule, definitionally baseRingModule. -/
theorem proper_field_finiteDimensional
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : X.Modules) [IsCoherentModule M] (n : ℕ) :
    letI := baseModule f M n
    FiniteDimensional k (H M n) := by
  letI := baseModule f M n
  exact proper_ext_finite f M n

/-- This is the exact boxed coefficient object used by existing rank and Euler lemmas. -/
theorem proper_baseFunctor_finiteDimensional
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : X.Modules) [IsCoherentModule M] (n : ℕ) :
    FiniteDimensional k ((baseFunctor f n).obj M) :=
  proper_field_finiteDimensional f M n

/-- Coherence is derived from original invertibility and actual properness. -/
theorem proper_invertible_ext_finite
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (L : InvertibleSheaf X) (n : ℕ) :
    letI := baseRingModule f L.obj n
    Module.Finite A (H L.obj n) := by
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_locallyOfFiniteType_toSpec f
  letI : IsCoherentModule L.obj := L.isCoherent
  exact proper_ext_finite f L.obj n

/-- Actual invertible coefficients over a proper field scheme meet the original finiteness type. -/
theorem proper_invertible_field_finiteDimensional
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L : InvertibleSheaf X) (n : ℕ) :
    letI := baseModule f L.obj n
    FiniteDimensional k (H L.obj n) := by
  letI := baseModule f L.obj n
  exact proper_invertible_ext_finite f L n

-- This checks the exact complete proposed telescope, not only a specialization.
example : ∀ {A : Type u} [instCommRing : CommRing A]
    [instNoetherianRing : IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [instProper : IsProper f]
    (M : X.Modules) [instCoherent : IsCoherentModule M] (n : ℕ),
    letI := baseRingRightDerivedModule f M n
    Module.Finite A (rightDerivedH M n) :=
  @KltDP.Literature.Stacks.properCohomology_finite.{u}

#check @KltDP.Literature.Stacks.properCohomology_finite
#print KltDP.Literature.Stacks.properCohomology_finite
#print axioms KltDP.Literature.Stacks.properCohomology_finite
#print proper_ext_finite
#print axioms proper_ext_finite
#print proper_field_finiteDimensional
#print axioms proper_field_finiteDimensional
#print proper_baseFunctor_finiteDimensional
#print axioms proper_baseFunctor_finiteDimensional
#print proper_invertible_ext_finite
#print axioms proper_invertible_ext_finite
#print proper_invertible_field_finiteDimensional
#print axioms proper_invertible_field_finiteDimensional

end KltDP.AdmissionProbe.ProperCohomologyConsumers
