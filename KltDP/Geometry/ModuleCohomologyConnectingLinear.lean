/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Vasily Ilin, Codex

Adapted from Vilin97/MazurTheorem commit
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/SchemeModuleCohomologyConnectingLinear.lean.
The connecting-map naturality wrapper is the corresponding ordinary
AINTLIB SheafCohomologyExact argument, using the reviewed pinned Ext-class
naturality port. The existing connecting map and canonical actions are kept.
-/

import KltDP.Geometry.ModuleCohomologyExact
import KltDP.Geometry.BaseFieldCohomology
import KltDP.Compatibility.ShortExactNaturality

/-!
# Canonical scalar linearity of the connecting homomorphism

Multiplication by a global function is a morphism of the original short
complex of scheme modules. Naturality of its Ext class therefore proves
linearity of the existing connecting homomorphism for the original
global-function action. Restriction along the actual structure morphism
gives base-field linearity, without changing the group or connecting map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian TopologicalSpace AlgebraicGeometry

universe w' w v u

namespace CategoryTheory.Sheaf.H

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrp.{w}] [HasExt.{w'} (Sheaf J AddCommGrp.{w})]

/-- Naturality of the existing connecting homomorphism, obtained by
postcomposing the naturality equation for the actual extension class. -/
theorem δ_naturality (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    {S₁ S₂ : ShortComplex (Sheaf J AddCommGrp.{w})}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)
    (x : H S₁.X₃ n₀) :
    δ h₂ n₀ n₁ h (map f.τ₃ n₀ x) = map f.τ₁ n₁ (δ h₁ n₀ n₁ h x) := by
  change (x.comp (Ext.mk₀ f.τ₃) (add_zero n₀)).comp h₂.extClass h =
    (x.comp h₁.extClass h).comp (Ext.mk₀ f.τ₁) (add_zero n₁)
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    ShortComplex.ShortExact.extClass_naturality h₁ h₂ f]

end CategoryTheory.Sheaf.H

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The same global scalar multiplies all three coefficient modules; their
original linear maps give the two commuting squares. -/
def globalSmulShortComplexHom {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (r : Γ(X, ⊤)) : S ⟶ S :=
  ShortComplex.homMk
    (globalSmulHom S.X₁ r)
    (globalSmulHom S.X₂ r)
    (globalSmulHom S.X₃ r)
    (globalSmulHom_naturality S.f r)
    (globalSmulHom_naturality S.g r)

/-- The already constructed connecting homomorphism is linear for the
canonical global-function actions in its two consecutive degrees. -/
def connectingLinearMap {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) :
    letI := globalSectionsCohomologyModule S.X₃ n
    letI := globalSectionsCohomologyModule S.X₁ (n + 1)
    H S.X₃ n →ₗ[Γ(X, ⊤)] H S.X₁ (n + 1) := by
  letI := globalSectionsCohomologyModule S.X₃ n
  letI := globalSectionsCohomologyModule S.X₁ (n + 1)
  refine
    { toFun := connecting S hS n
      map_add' := (connecting S hS n).map_add
      map_smul' := ?_ }
  intro r x
  rw [globalSectionsCohomologyModule_smul, globalSectionsCohomologyModule_smul]
  let T := S.map (SheafOfModules.toSheaf X.ringCatSheaf)
  let hT : T.ShortExact := KltDP.Sheaf.schemeModule_shortExact_toSheaf X S hS
  let φ : T ⟶ T :=
    (SheafOfModules.toSheaf X.ringCatSheaf).mapShortComplex.map
      (globalSmulShortComplexHom S r)
  have hnatural := CategoryTheory.Sheaf.H.δ_naturality n (n + 1) rfl hT hT φ x
  change connecting S hS n
      ((zariskiFunctor X n).map (globalSmulHom S.X₃ r) x) =
    (zariskiFunctor X (n + 1)).map (globalSmulHom S.X₁ r)
      (connecting S hS n x) at hnatural
  exact hnatural

/-- The linear map has exactly the original connecting function. -/
theorem connectingLinearMap_apply {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) (x : H S.X₃ n) :
    letI := globalSectionsCohomologyModule S.X₃ n
    letI := globalSectionsCohomologyModule S.X₁ (n + 1)
    connectingLinearMap S hS n x = connecting S hS n x := rfl

/-- Base-field linearity uses the original structure morphism to restrict
the proved global-function linearity. -/
def connectingBaseLinearMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) :
    letI := baseModule f S.X₃ n
    letI := baseModule f S.X₁ (n + 1)
    H S.X₃ n →ₗ[k] H S.X₁ (n + 1) := by
  letI := globalSectionsCohomologyModule S.X₃ n
  letI := globalSectionsCohomologyModule S.X₁ (n + 1)
  letI := baseModule f S.X₃ n
  letI := baseModule f S.X₁ (n + 1)
  refine
    { toFun := connecting S hS n
      map_add' := (connecting S hS n).map_add
      map_smul' := ?_ }
  intro r x
  exact (connectingLinearMap S hS n).map_smul (baseFieldToGlobalSections f r) x

/-- Restricting scalars leaves the connecting function unchanged. -/
theorem connectingBaseLinearMap_apply {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ) (x : H S.X₃ n) :
    letI := baseModule f S.X₃ n
    letI := baseModule f S.X₁ (n + 1)
    connectingBaseLinearMap f S hS n x = connecting S hS n x := rfl

end KltDP.Geometry.ModuleCohomology
