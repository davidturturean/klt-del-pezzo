/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

The restricted-unit/counit comparison adapts the proved open-restriction
route in CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/ForMathlib/PullbackTensorMonoidal.lean.
For the over-site, the pinned Mathlib cocontinuity and preservation of
local bijectivity replace the scheme-specific covering-sieve proof.
-/
import KltDP.Compatibility.SheafLocalBasis
import KltDP.Compatibility.SheafModuleMonoidal
import KltDP.Compatibility.PresheafRestrictionTensor
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Actual over-site restriction of sheafification and tensor products

Restriction along `Over.forget U` preserves local bijectivity. Therefore
the restricted sheafification unit becomes an isomorphism after
sheafification on the over-site. Its inverse and the actual counit give
the comparison of restriction with sheafification. The existing
presheaf and sheaf tensor comparisons then give the actual sheaf tensor
isomorphism. No compatibility or gluing result is assumed.
-/

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace KltDP.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

section Sheafification

variable (R : Sheaf J RingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [HasWeakSheafify J AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]

/-- The restricted sheafification unit is inverted by sheafification on
the actual over-site. This follows from the pinned cocontinuity theorem. -/
theorem over_sheafificationUnit_mem (U : C) (P : PresheafOfModules.{u} R.val) :
    PresheafOfModules.sheafificationW (𝟙 (R.over U).val)
      ((PresheafOfModules.pushforward₀ (Over.forget U) R.val).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.val)).unit.app P)) := by
  rw [PresheafOfModules.sheafificationW_iff_isLocallyBijective]
  constructor
  · change Presheaf.IsLocallyInjective (J.over U)
      (whiskerLeft (Over.forget U).op (CategoryTheory.toSheafify J P.presheaf))
    exact Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  · change Presheaf.IsLocallySurjective (J.over U)
      (whiskerLeft (Over.forget U).op (CategoryTheory.toSheafify J P.presheaf))
    exact Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _

/-- Restriction of actual module sheafification agrees with sheafification
of the restricted presheaf. The comparison uses the restricted unit and
the actual sheafification counit. -/
noncomputable def overSheafificationIso (U : C) (P : PresheafOfModules.{u} R.val) :
    ((PresheafOfModules.sheafification (𝟙 R.val)).obj P).over U ≅
      (PresheafOfModules.sheafification (𝟙 (R.over U).val)).obj
        ((PresheafOfModules.pushforward₀ (Over.forget U) R.val).obj P) := by
  have hmem := over_sheafificationUnit_mem R U P
  rw [PresheafOfModules.sheafificationW_iff] at hmem
  exact
    (PresheafOfModules.sheafificationForgetIso (R.over U)
      (((PresheafOfModules.sheafification (𝟙 R.val)).obj P).over U)).symm ≪≫
    (@asIso _ _ _ _ _ hmem).symm

end Sheafification

section Tensor

variable (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

include hS in
/-- The commutative-ring presheaf on the actual over-site has the sheaf
condition inherited from restriction of the original ring sheaf. -/
theorem overRingSheafCondition (U : C) :
    Presheaf.IsSheaf (J.over U)
      (((Over.forget U).op ⋙ S) ⋙ forget₂ CommRingCat RingCat) :=
  ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U).cond

variable [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [HasWeakSheafify J AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{u}]

/-- Actual restriction to the over-site preserves the localized tensor
product of module sheaves. -/
noncomputable def overTensorIso (U : C)
    (M N : _root_.SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    letI : MonoidalCategory (_root_.SheafOfModules.{u}
        ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U)) :=
      PresheafOfModules.sheafOfModulesMonoidalCategory
        ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
    (M ⊗ N).over U ≅ M.over U ⊗ N.over U := by
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI : MonoidalCategory (_root_.SheafOfModules.{u}
      ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U)) :=
    PresheafOfModules.sheafOfModulesMonoidalCategory
      ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
  exact
    (_root_.SheafOfModules.overFunctor
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U).mapIso
      (PresheafOfModules.sheafTensorIsoSheafification S hS M N) ≪≫
    overSheafificationIso
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U
      (M.val ⊗ N.val) ≪≫
    (PresheafOfModules.sheafification
      (𝟙 ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U).val)).mapIso
      (PresheafOfModules.overTensorIso S U M.val N.val) ≪≫
    (PresheafOfModules.sheafTensorIsoSheafification
      ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
      (M.over U) (N.over U)).symm

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- Actual restriction preserves the chosen monoidal tensor unit, through
the counit comparisons with the original ring sheaves. -/
noncomputable def overTensorUnitIso (U : C) :
    letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
    letI : MonoidalCategory (_root_.SheafOfModules.{u}
        ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U)) :=
      PresheafOfModules.sheafOfModulesMonoidalCategory
        ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
    (𝟙_ (_root_.SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}))).over U ≅
      𝟙_ (_root_.SheafOfModules.{u}
        ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U)) := by
  letI := PresheafOfModules.sheafOfModulesMonoidalCategory S hS
  letI : MonoidalCategory (_root_.SheafOfModules.{u}
      ((⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).over U)) :=
    PresheafOfModules.sheafOfModulesMonoidalCategory
      ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)
  exact
    (_root_.SheafOfModules.overFunctor
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}) U).mapIso
      (PresheafOfModules.sheafTensorUnitIso S hS) ≪≫
    _root_.SheafOfModules.unitOverIso
      (R := (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) U ≪≫
    (PresheafOfModules.sheafTensorUnitIso
      ((Over.forget U).op ⋙ S) (overRingSheafCondition S hS U)).symm

end Tensor

end KltDP.SheafOfModules
