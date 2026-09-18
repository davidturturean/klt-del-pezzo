import KltDP.Geometry.TopExteriorBaseChange
import KltDP.LinearAlgebra.ExteriorPowerScalarMap
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization of the original top exterior scalar map

The existing finite-free exterior base-change equivalence and the pinned
localization/base-change equivalence prove that the original exterior scalar
map is itself a module localization. Its action on every native wedge is
unchanged. This supplies an inverse for the actual localization evaluation,
without an independently chosen line isomorphism.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace KltDP.LinearAlgebra.TopExteriorScalarLocalization

variable {R : Type u} [CommRing R] (S : Submonoid R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f]
    {n : ℕ} (b : Basis (Fin n) R M)

private def equiv : A ⊗[R] (⋀[R]^n M) ≃ₗ[A] (⋀[A]^n N) :=
  (KltDP.Geometry.TopExteriorBaseChange.equiv A b).trans
    (((ModuleCat.exteriorPower.functor A n).mapIso
      (IsLocalizedModule.isBaseChange S A f).equiv.toModuleIso).toLinearEquiv)

private theorem equiv_comp_mk :
    ((equiv S A f b).toLinearMap.restrictScalars R).comp
        (TensorProduct.mk R A (⋀[R]^n M) 1) =
      ExteriorPowerScalarMap.map R A n f := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.map n (IsLocalizedModule.isBaseChange S A f).equiv.toLinearMap
      (KltDP.Geometry.TopExteriorBaseChange.equiv A b
        ((1 : A) ⊗ₜ[R] exteriorPower.ιMulti R n v)) =
    ExteriorPowerScalarMap.map R A n f (exteriorPower.ιMulti R n v)
  rw [KltDP.Geometry.TopExteriorBaseChange.equiv_one_tmul_ιMulti,
    exteriorPower.map_apply_ιMulti, ExteriorPowerScalarMap.map_ιMulti]
  apply congrArg (exteriorPower.ιMulti A n)
  funext i
  exact ((IsLocalizedModule.isBaseChange S A f).equiv_tmul 1 (v i)).trans
    (one_smul A (f (v i)))

include b in
/-- The original top exterior scalar map is a localization when the
original module map is a localization and its source has the stated basis. -/
theorem isLocalizedModule :
    IsLocalizedModule S (ExteriorPowerScalarMap.map R A n f) := by
  apply (isLocalizedModule_iff_isBaseChange S A
    (ExteriorPowerScalarMap.map R A n f)).mpr
  refine IsBaseChange.of_equiv (equiv S A f b) fun x => ?_
  exact LinearMap.congr_fun (equiv_comp_mk S A f b) x

end KltDP.LinearAlgebra.TopExteriorScalarLocalization

#check @KltDP.LinearAlgebra.TopExteriorScalarLocalization.isLocalizedModule
#print axioms KltDP.LinearAlgebra.TopExteriorScalarLocalization.isLocalizedModule
