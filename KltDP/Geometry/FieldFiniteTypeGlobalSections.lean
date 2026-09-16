/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.SheafModuleFiniteTypeOnPoint
import KltDP.Geometry.AffineModuleGlobalSections
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Actual global sections of finite-type sheaves on a field spectrum

The one-point argument supplies finite generation over the original global
section ring. Its canonical isomorphism with the field then gives finite
generation for the existing `AffineModuleTilde.sectionModule` scalar action.
No quasicoherence or global-finiteness premise is inserted. In the separate
quasicoherent application, the original affine counit identifies the tilde of
this same finite module with the original sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k : Type u) [Field k]

/-- The original finite-type sheaf on Spec k has finite actual global sections
for the original base-field action. -/
theorem globalSections_finite_of_isFiniteType (M : (Spec (.of k)).Modules)
    [_root_.SheafOfModules.IsFiniteType M] :
    Module.Finite k (sectionModule M ⊤) := by
  let A := Γ(Spec (.of k), ⊤)
  letI : Module A (sectionModule M ⊤) := (M.val.obj (op ⊤)).isModule
  letI : Module.Finite A (sectionModule M ⊤) :=
    KltDP.SheafModuleFiniteTypeOnPoint.top_finite_of_isFiniteType M
  let e := Scheme.ΓSpecIso (CommRingCat.of k)
  letI : Algebra k A := e.inv.hom.toAlgebra
  letI : Module.Finite k A :=
    Module.Finite.of_surjective (Algebra.linearMap k A)
      (ConcreteCategory.bijective_of_isIso e.inv).2
  letI : IsScalarTower k A (sectionModule M ⊤) :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := sectionModule M ⊤)
      (fun r s => (sectionModule_smul_toOpen M ⊤ r s).symm)
  exact Module.Finite.trans A (sectionModule M ⊤)

end KltDP.Geometry.AffineModuleTilde
