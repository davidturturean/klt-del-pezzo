/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Exactness of the underlying additive sheaf functor

The reflector argument is adapted from AINTLIB's `SchemeModuleSheaf.lean`
at `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`, retained in MazurTheorem
`9327963d4ec14fba49c7b14b004fd00707ffc2e9`. We apply it directly to the
pinned `SheafOfModules.toSheaf`, for an arbitrary sheaf of rings.

The module-sheafification reflector commutes with forgetting the module
action. Both functors in the resulting additive-presheaf composite preserve
colimits. The reflector's counit then proves colimit preservation on actual
module sheaves. Together with the pinned finite-limit instance, this carries
a short exact sequence of module sheaves to a short exact sequence of
additive sheaves; no underlying exactness premise is required.
-/

noncomputable section

open CategoryTheory Limits

universe w w' v v' u u' u₁ u₂ u₃ v₁ v₂ v₃

namespace KltDP.Sheaf

/-- Colimit preservation descends from the composite with a reflector.
The proof uses actual colimit cocones and the isomorphism given by its counit. -/
private theorem preservesColimitsOfShape_of_reflector_comp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (R : C ⥤ D) [Reflective R]
    {K : Type w} [Category.{w'} K] (F : C ⥤ E)
    [PreservesColimitsOfShape K (reflector R ⋙ F)] [HasColimitsOfShape K D] :
    PreservesColimitsOfShape K F := by
  constructor
  intro G
  refine @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _
    (NatIso.hcomp (asIso (𝟙 G)) (asIso (reflectorAdjunction R).counit).symm).symm
      ⟨fun hc ↦ ⟨?_⟩⟩
  let hc₂ := colimit.isColimit (G ⋙ R)
  let ψ := IsColimit.uniqueUpToIso (isColimitOfPreserves (reflector R) hc₂) hc
  have φ := IsColimit.ofIsoColimit
    (isColimitOfPreserves (reflector R ⋙ F) hc₂)
    (Functor.mapCoconeMapCocone (H := reflector R) (H' := F)
      (colimit.cocone (G ⋙ R))).symm
  exact IsColimit.ofIsoColimit φ ((Cocones.functoriality _ F).mapIso ψ)

section Site

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : CategoryTheory.Sheaf J RingCat.{u})

/-- Forgetting the action on actual module sheaves preserves any shape of
colimits available in the category of their additive sections. -/
theorem toSheaf_preservesColimitsOfShape
    [HasWeakSheafify J AddCommGrp.{v}] [J.WEqualsLocallyBijective AddCommGrp.{v}]
    (K : Type w) [Category.{w'} K] [HasColimitsOfShape K AddCommGrp.{v}] :
    PreservesColimitsOfShape K (SheafOfModules.toSheaf.{v} R) := by
  letI : Reflective (SheafOfModules.forget.{v} R) :=
    { L := PresheafOfModules.sheafification (𝟙 R.val)
      adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.val) }
  haveI : PreservesColimitsOfShape K
      (reflector (SheafOfModules.forget.{v} R) ⋙ SheafOfModules.toSheaf R) :=
    comp_preservesColimitsOfShape
      (PresheafOfModules.toPresheaf R.val) (presheafToSheaf J AddCommGrp)
  exact preservesColimitsOfShape_of_reflector_comp (SheafOfModules.forget R) _

instance toSheaf_preservesFiniteColimits
    [HasWeakSheafify J AddCommGrp.{v}] [J.WEqualsLocallyBijective AddCommGrp.{v}] :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{v} R) where
  preservesFiniteColimits K _ _ := toSheaf_preservesColimitsOfShape R K

/-- An actual short exact sequence of module sheaves is short exact after
forgetting the action. In particular its right-hand map remains an epimorphism. -/
theorem shortExact_toSheaf
    [HasSheafify J AddCommGrp.{v}] [J.WEqualsLocallyBijective AddCommGrp.{v}]
    (S : ShortComplex (SheafOfModules.{v} R)) (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf R)).ShortExact :=
  hS.map_of_exact (SheafOfModules.toSheaf R)

end Site

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The specialization uses the scheme's original ring sheaf and the same
underlying additive-sheaf functor used in its Ext-based cohomology. -/
theorem schemeModule_shortExact_toSheaf (X : AlgebraicGeometry.Scheme.{u})
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf X.ringCatSheaf)).ShortExact :=
  shortExact_toSheaf X.ringCatSheaf S hS

end KltDP.Sheaf
