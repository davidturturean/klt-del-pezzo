import KltDP.Geometry.ModuleCohomologyEuler
import KltDP.Geometry.SurfaceCohomologyVanishing
import KltDP.Geometry.ProjectiveProper
import KltDP.AdmissionProbe.ProperCohomologyConsumers
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Euler characteristic of an actual binary direct sum on a surface

The native base-field cohomology functor carries the original sheaf
biproduct to the product of its original cohomology modules. Proper
cohomology finiteness and surface vanishing supply every finiteness and
boundedness condition for coherent coefficients. No Euler identity or
cohomological decomposition is assumed.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

private theorem originalBaseFunctor_additive (n : ℕ) : (baseFunctor f n).Additive := by
  constructor
  intro M N a b
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (zariskiFunctor X n).map (a + b) x =
    (zariskiFunctor X n).map a x + (zariskiFunctor X n).map b x
  exact ConcreteCategory.congr_hom ((zariskiFunctor X n).map_add (f := a) (g := b)) x

/-- The cohomology of the actual sheaf biproduct, over the original field. -/
def baseCohomologyBiprodLinearEquiv (M N : X.Modules) (n : ℕ) :
    (baseFunctor f n).obj (M ⊞ N) ≃ₗ[k]
      ((baseFunctor f n).obj M × (baseFunctor f n).obj N) := by
  letI := originalBaseFunctor_additive f n
  letI : PreservesBinaryBiproduct M N (baseFunctor f n) :=
    preservesBinaryBiproduct_of_preservesBiproduct (baseFunctor f n) M N
  exact ((baseFunctor f n).mapBiprod M N ≪≫
    ModuleCat.biprodIsoProd ((baseFunctor f n).obj M) ((baseFunctor f n).obj N)).toLinearEquiv

/-- Finite-dimensional native cohomology has the actual direct-sum dimension. -/
theorem cohomologyDimension_biprod (M N : X.Modules) (n : ℕ)
    [FiniteDimensional k ((baseFunctor f n).obj M)]
    [FiniteDimensional k ((baseFunctor f n).obj N)] :
    cohomologyDimension f (M ⊞ N) n =
      cohomologyDimension f M n + cohomologyDimension f N n := by
  change Module.finrank k ((baseFunctor f n).obj (M ⊞ N)) =
    Module.finrank k ((baseFunctor f n).obj M) + Module.finrank k ((baseFunctor f n).obj N)
  rw [(baseCohomologyBiprodLinearEquiv f M N n).finrank_eq, Module.finrank_prod]

end KltDP.Geometry.ModuleCohomology

namespace KltDP.Geometry.NormalProjectiveSurface

open ModuleCohomology

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

/-- Native Euler characteristic is additive for two actual coherent
coefficients on the original normal projective surface. -/
theorem eulerCharacteristic_biprod (M N : S.toScheme.Modules)
    [IsCoherentModule M] [IsCoherentModule N] :
    eulerCharacteristic S.structureMorphism (M ⊞ N) =
      eulerCharacteristic S.structureMorphism M + eulerCharacteristic S.structureMorphism N := by
  letI : IsProper S.structureMorphism := S.projective.isProper
  rw [eulerCharacteristic_eq_truncatedEuler S.structureMorphism (M ⊞ N) 2
      (normalProjectiveSurface_H_subsingleton S (M ⊞ N)),
    eulerCharacteristic_eq_truncatedEuler S.structureMorphism M 2
      (normalProjectiveSurface_H_subsingleton S M),
    eulerCharacteristic_eq_truncatedEuler S.structureMorphism N 2
      (normalProjectiveSurface_H_subsingleton S N)]
  unfold truncatedEuler
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  letI := KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional
    S.structureMorphism M n
  letI := KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional
    S.structureMorphism N n
  rw [cohomologyDimension_biprod]
  simp only [Nat.cast_add, mul_add]

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.eulerCharacteristic_biprod
#print axioms KltDP.Geometry.ModuleCohomology.baseCohomologyBiprodLinearEquiv
#print axioms KltDP.Geometry.NormalProjectiveSurface.eulerCharacteristic_biprod
