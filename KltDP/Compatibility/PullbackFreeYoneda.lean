/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

Selective port of MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/AINTLIB/Picard/Pullback.lean:920-1033, retaining
AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684. This uses the pinned
actual pullback adjunction and corepresentability of free representables.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-!
# Actual pullback of free representable module presheaves

The existing pullback carries the free representable at U to the free
representable at its image. The explicit comparison and generator formulas
are proved from the actual adjunction, with no tensor comparison assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace PresheafOfModules

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section PullbackFreeYoneda

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- The presheaf pullback of a
free-yoneda module is the free-yoneda module of the image object: both corepresent the
functor `M ↦ ((push M).obj X ≃ M.obj (F X))`, by the adjunction and by mathlib's
`pushforwardCompCoyonedaFreeYonedaCorepresentableBy` respectively. -/
noncomputable def pullbackFreeYonedaIso (X : C) :
    (pullback.{u} φ).obj ((free S).obj (yoneda.obj X)) ≅
      (free R).obj (yoneda.obj (F.obj X)) where
  hom := ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm
    ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv (𝟙 _))
  inv := (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv.symm
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (𝟙 _))
  hom_inv_id := ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    change ((pushforward φ ⋙ coyoneda.obj (Opposite.op ((free S).obj (yoneda.obj X)))).map
      ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv.symm
        ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (𝟙 _)))
      ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv (𝟙 _))) = _
    rw [← Functor.CorepresentableBy.homEquiv_eq, Equiv.apply_symm_apply])
  inv_hom_id := (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv.injective (by
    rw [Functor.CorepresentableBy.homEquiv_comp, Equiv.apply_symm_apply]
    change (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (𝟙 _) ≫
      (pushforward φ).map (((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm
        ((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv (𝟙 _))) = _
    rw [← Adjunction.homEquiv_naturality_right, Category.id_comp, Equiv.apply_symm_apply])

/-- Characterization of `pullbackFreeYonedaIso`: postcomposition with a map `g` out of the
corepresenting free-yoneda corresponds, under the adjunction, to the generator image of
`g` viewed in the pushforward. This is the compute rule for the [G3-pre] δ-chase. -/
lemma homEquiv_pullbackFreeYonedaIso_hom_comp {X : C} {N : PresheafOfModules.{u} R}
    (g : (free R).obj (yoneda.obj (F.obj X)) ⟶ N) :
    (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _
        ((pullbackFreeYonedaIso φ X).hom ≫ g) =
      (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv g := by
  rw [Adjunction.homEquiv_naturality_right]
  change ((pushforward φ ⋙ coyoneda.obj (Opposite.op ((free S).obj (yoneda.obj X)))).map g
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (pullbackFreeYonedaIso φ X).hom)) = _
  rw [show (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (pullbackFreeYonedaIso φ X).hom =
      (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv (𝟙 _) from
    Equiv.apply_symm_apply _ _]
  rw [← Functor.CorepresentableBy.homEquiv_eq]

/-- Evaluation form of `freeYonedaEquiv`: the value of a map out of a free-yoneda module is
its value on the generator `freeMk (𝟙 X)`. -/
lemma freeYonedaEquiv_apply {M : PresheafOfModules.{u} S} {X : C}
    (g : (free S).obj (yoneda.obj X) ⟶ M) :
    freeYonedaEquiv g = g.app (Opposite.op X) (ModuleCat.freeMk (𝟙 X)) := by
  obtain ⟨x, rfl⟩ := freeYonedaEquiv.symm.surjective g
  rw [Equiv.apply_symm_apply, freeYonedaEquiv_symm_app]

/-- Generator evaluation of the corepresentability equivalence: the transposed morphism,
evaluated on the upstairs generator, is the generator image of the original morphism. -/
lemma corepresentableBy_homEquiv_app_generator {X : C} {N : PresheafOfModules.{u} R}
    (g : (free R).obj (yoneda.obj (F.obj X)) ⟶ N) :
    (((pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv g :
        (free S).obj (yoneda.obj X) ⟶ (pushforward.{u} φ).obj N)).app
        (Opposite.op X) (ModuleCat.freeMk (𝟙 X)) =
      (freeYonedaEquiv g : N.obj (Opposite.op (F.obj X))) := by
  rw [← freeYonedaEquiv_apply]
  exact Equiv.apply_symm_apply _ _

/-- The adjunction unit at a free-yoneda module, through the corepresentability of the
pullback: the `homEquiv`-transposed inverse of `pullbackFreeYonedaIso`. This is the compute
rule for units in the [G3-pre]/[G3-η] generator chases. -/
lemma unit_app_freeYoneda (X : C) :
    (pullbackPushforwardAdjunction.{u} φ).unit.app ((free S).obj (yoneda.obj X)) =
      (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).homEquiv
        ((pullbackFreeYonedaIso φ X).inv) := by
  rw [← Adjunction.homEquiv_id, ← Iso.hom_inv_id (pullbackFreeYonedaIso φ X),
    homEquiv_pullbackFreeYonedaIso_hom_comp]

/-- The free presheaf's restriction on generators, over an arbitrary `RingCat`-valued
ring presheaf. -/
lemma freeObj_map_freeMk' {R' : Cᵒᵖ ⥤ RingCat.{u}} {H : Cᵒᵖ ⥤ Type u} {V W : Cᵒᵖ}
    (i : V ⟶ W) (x : H.obj V) :
    ((free R').obj H).map i (ModuleCat.freeMk x) =
      (ModuleCat.freeMk (H.map i x) : ((free R').obj H).obj W) := by
  erw [ModuleCat.freeDesc_apply]

/-- Evaluation of a morphism out of a free-yoneda module on an arbitrary generator
`freeMk h`: the restriction of its generator image along `h`. The one compute rule for
both sides of the [G3-pre] δ-chase. -/
lemma app_freeMk {R' : Cᵒᵖ ⥤ RingCat.{u}} {U : C} {N : PresheafOfModules.{u} R'}
    (g : (free R').obj (yoneda.obj U) ⟶ N) {W : C} (h : W ⟶ U) :
    g.app (Opposite.op W) (ModuleCat.freeMk h) =
      N.map h.op (freeYonedaEquiv g) := by
  let idU : (yoneda.obj U).obj (Opposite.op U) := 𝟙 U
  let genU : ((free R').obj (yoneda.obj U)).obj (Opposite.op U) :=
    ModuleCat.freeMk idU
  have hh : (ModuleCat.freeMk h : ((free R').obj (yoneda.obj U)).obj (Opposite.op W)) =
      ((free R').obj (yoneda.obj U)).map h.op genU := by
    rw [freeObj_map_freeMk']
    change ModuleCat.freeMk h = ModuleCat.freeMk ((yoneda.obj U).map h.op idU)
    exact congrArg ModuleCat.freeMk (by simp [idU])
  rw [hh, naturality_apply]
  congr 1

/-- The generator image of the adjunction unit at a free-yoneda module is the generator
image of the corepresentability comparison. -/
lemma freeYonedaEquiv_unit_app (X : C) :
    freeYonedaEquiv ((pullbackPushforwardAdjunction.{u} φ).unit.app
        ((free S).obj (yoneda.obj X))) =
      freeYonedaEquiv ((pullbackFreeYonedaIso φ X).inv) := by
  rw [unit_app_freeYoneda, freeYonedaEquiv_apply]
  exact corepresentableBy_homEquiv_app_generator φ ((pullbackFreeYonedaIso φ X).inv)

end PullbackFreeYoneda

end PresheafOfModules
