/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

Selective port of MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/AINTLIB/Picard/Pullback.lean:552-842, itself retaining
AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684. The pointwise free-module
comparison below reuses the pinned ModuleCat free monoidal structure.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Tensor products of free presheaves and open representables

The free module functor carries pointwise products of sets to tensor
products of modules. On the category of opens, intersections represent
products of representables. Both comparisons are constructed here on
actual presheaves, including their section maps.
-/

noncomputable section

universe v₁ u₁ u

open CategoryTheory MonoidalCategory Functor
open scoped TensorProduct

namespace PresheafOfModules

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section FreeYonedaTensor

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The meet equivalence of hom-types in a meet-semilattice category (all four types are
subsingletons). -/
def meetHomEquiv (U₁ U₂ V : X.Opens) :
    ((V ⟶ U₁) × (V ⟶ U₂)) ≃ (V ⟶ U₁ ⊓ U₂) where
  toFun p := homOfLE (le_inf (leOfHom p.1) (leOfHom p.2))
  invFun h := (homOfLE ((leOfHom h).trans inf_le_left),
    homOfLE ((leOfHom h).trans inf_le_right))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- On the category of opens, the pointwise product of
two representables is represented by the meet: `Hom(V,U₁) × Hom(V,U₂) ≅ Hom(V, U₁ ⊓ U₂)`. -/
noncomputable def yonedaMeetIso (U₁ U₂ : X.Opens) :
    (yoneda.obj U₁ ⊗ yoneda.obj U₂ : (X.Opens)ᵒᵖ ⥤ Type u) ≅ yoneda.obj (U₁ ⊓ U₂) :=
  NatIso.ofComponents
    (fun V => Equiv.toIso (meetHomEquiv U₁ U₂ V.unop))
    (fun {V W} f => by
      haveI : Subsingleton ((yoneda.obj (U₁ ⊓ U₂)).obj W) :=
        inferInstanceAs (Subsingleton (W.unop ⟶ U₁ ⊓ U₂))
      ext p
      exact Subsingleton.elim _ _)

section FreeTensorGeneric

variable {C : Type u₁} [Category.{v₁} C] (T : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The pointwise component of the free–tensor comparison, hint-typed at the presheaf
carriers (`finsuppTensorFinsupp'`; both directions send generators to generators). -/
noncomputable def freeTensorμ (F G : Cᵒᵖ ⥤ Type u) (V : Cᵒᵖ) :
    (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj V) ≅
      (((free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G)).obj V) :=
  Functor.Monoidal.μIso
    (ModuleCat.free (↑((T ⋙ forget₂ CommRingCat RingCat).obj V)))
    (F.obj V) (G.obj V)

@[simp]
lemma freeTensorμ_hom_freeMk_tmul (F G : Cᵒᵖ ⥤ Type u) (V : Cᵒᵖ)
    (x : F.obj V) (y : G.obj V) :
    (freeTensorμ T F G V).hom (ModuleCat.freeMk x ⊗ₜ ModuleCat.freeMk y) =
      (ModuleCat.freeMk ((x, y) : (F ⊗ G).obj V) :
        ((free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G)).obj V) :=
  ModuleCat.free_μ_freeMk_tmul_freeMk _ x y

@[simp]
lemma freeTensorμ_inv_freeMk (F G : Cᵒᵖ ⥤ Type u) (V : Cᵒᵖ) (z : (F ⊗ G).obj V) :
    (freeTensorμ T F G V).inv (ModuleCat.freeMk z) =
      (ModuleCat.freeMk z.1 ⊗ₜ ModuleCat.freeMk z.2 :
        (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
          (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj V)) :=
  ModuleCat.free_δ_freeMk _ z

/-- The free presheaf's restriction on generators: `freeMk x ↦ freeMk (F.map f x)`. -/
@[simp]
lemma freeObj_map_freeMk {H : Cᵒᵖ ⥤ Type u} {V W : Cᵒᵖ} (f : V ⟶ W) (x : H.obj V) :
    ((free (T ⋙ forget₂ CommRingCat RingCat)).obj H).map f (ModuleCat.freeMk x) =
      (ModuleCat.freeMk (H.map f x) :
        ((free (T ⋙ forget₂ CommRingCat RingCat)).obj H).obj W) := by
  erw [ModuleCat.freeDesc_apply]

/-- Elementwise form of the tensor product of morphisms of presheaves of modules. -/
lemma tensorHom_app_tmul {M₁ M₂ M₃ M₄ :
      PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)}
    (g₁ : M₁ ⟶ M₂) (g₂ : M₃ ⟶ M₄) (V : Cᵒᵖ) (x : M₁.obj V) (y : M₃.obj V) :
    (g₁ ⊗ g₂).app V (x ⊗ₜ y) = (g₁.app V x ⊗ₜ g₂.app V y : (M₂ ⊗ M₄).obj V) :=
  ModuleCat.MonoidalCategory.tensorHom_tmul (g₁.app V) (g₂.app V) x y

/-- The free presheaf functor on morphisms, on generators:
`(free R).map g` sends `freeMk x` to `freeMk (g.app x)`. -/
@[simp]
lemma free_map_app_freeMk {F G : Cᵒᵖ ⥤ Type u} (g : F ⟶ G) (V : Cᵒᵖ) (x : F.obj V) :
    (((free (T ⋙ forget₂ CommRingCat RingCat)).map g).app V) (ModuleCat.freeMk x) =
      (ModuleCat.freeMk (g.app V x) :
        ((free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj V) := by
  erw [ModuleCat.free_map_apply]

/-- `ModuleCat.free_hom_ext`, restated at the presheaf-of-modules clothing of the free
objects (the mathlib form's `(ModuleCat.free R).obj`-spelling reframes goals and poisons
`kabstract`; the defeq crossing happens once, here, at elaboration). -/
lemma clothedFree_hom_ext {H : Cᵒᵖ ⥤ Type u} {V : Cᵒᵖ}
    {M : ModuleCat ↑((T ⋙ forget₂ CommRingCat RingCat).obj V)}
    {f g : ((free (T ⋙ forget₂ CommRingCat RingCat)).obj H).obj V ⟶ M}
    (h : ∀ x : H.obj V, f (ModuleCat.freeMk x) = g (ModuleCat.freeMk x)) : f = g :=
  ModuleCat.free_hom_ext h

/-- The types-level pairing `(x, y) ↦ freeMk x ⊗ₜ freeMk y`, the adjunct of the free–tensor
comparison. Naturality is an elementwise Types-square. -/
noncomputable def freeTensorPair (F G : Cᵒᵖ ⥤ Type u) :
    (F ⊗ G) ⟶
      ((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).presheaf ⋙ forget _ where
  app V := fun z =>
    ((ModuleCat.freeMk z.1 ⊗ₜ ModuleCat.freeMk z.2 :
      (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj V)))
  naturality {V W} f := by
    ext z
    change (ModuleCat.freeMk (F.map f z.1) ⊗ₜ
        ModuleCat.freeMk (G.map f z.2) :
        (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
          (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).obj W)) =
      (((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G).map f)
        (ModuleCat.freeMk z.1 ⊗ₜ ModuleCat.freeMk z.2)
    erw [Monoidal.tensorObj_map_tmul]
    rw [freeObj_map_freeMk T f z.1, freeObj_map_freeMk T f z.2]
    rfl

/-- The free–tensor comparison out of the free presheaf, by the universal property
(naturality supplied by `freeObjDesc`). -/
noncomputable def freeTensorDesc (F G : Cᵒᵖ ⥤ Type u) :
    (free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G) ⟶
      ((free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G) :=
  freeObjDesc (freeTensorPair T F G)

/-- The free–tensor comparison agrees componentwise with the pointwise
`finsuppTensorFinsupp'` isomorphism (both send generators to generators). -/
lemma freeTensorDesc_app (F G : Cᵒᵖ ⥤ Type u) (V : Cᵒᵖ) :
    (freeTensorDesc T F G).app V = (freeTensorμ T F G V).inv := by
  refine clothedFree_hom_ext T (fun z => ?_)
  rw [freeTensorμ_inv_freeMk T F G V z]
  simp only [freeTensorDesc, freeObjDesc_app, freeTensorPair]
  erw [ModuleCat.freeDesc_apply]

instance (F G : Cᵒᵖ ⥤ Type u) : IsIso (freeTensorDesc T F G) := by
  haveI : ∀ V : Cᵒᵖ, IsIso ((freeTensorDesc T F G).app V) := fun V => by
    rw [freeTensorDesc_app T F G V]; infer_instance
  haveI : IsIso ((toPresheaf _).map (freeTensorDesc T F G)) := by
    haveI : ∀ V : Cᵒᵖ, IsIso (((toPresheaf _).map (freeTensorDesc T F G)).app V) := fun V =>
      inferInstanceAs (IsIso ((forget₂ _ AddCommGrp).map ((freeTensorDesc T F G).app V)))
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (toPresheaf (T ⋙ forget₂ CommRingCat RingCat))

/-- The free presheaf of modules functor
is monoidal on tensor products: `free(F ⊗ G) ≅ free(F) ⊗ free(G)`, with hom sending the
generator `freeMk (x, y)` to `freeMk x ⊗ₜ freeMk y` (see `freeTensorDesc_app` /
`freeTensorμ_inv_freeMk`). -/
noncomputable def freeTensorIso (F G : Cᵒᵖ ⥤ Type u) :
    ((free (T ⋙ forget₂ CommRingCat RingCat)).obj (F ⊗ G) :
        PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)) ≅
      (free (T ⋙ forget₂ CommRingCat RingCat)).obj F ⊗
        (free (T ⋙ forget₂ CommRingCat RingCat)).obj G :=
  asIso (freeTensorDesc T F G)

end FreeTensorGeneric

/-- On the category of opens of a scheme, the
presheaf tensor of two free-yoneda presheaves of modules is the free-yoneda of the meet:
pointwise, `Hom(V,U₁) × Hom(V,U₂) = [V ≤ U₁ ⊓ U₂]` (a meet-semilattice has representable
products of representables), and the free-module functor sends products of types to tensor
products of free modules (`finsuppTensorFinsupp`-style). Together with mathlib's
`freeFunctorCompPullbackIso` this makes the oplax comparison `δ` an isomorphism on free-yoneda
pairs — before sheafifying. -/
noncomputable def freeYonedaTensorIso (U₁ U₂ : X.Opens) :
    ((free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₁) ⊗
        (free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U₂) :
          PresheafOfModules.{u} (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) ≅
      (free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj (U₁ ⊓ U₂)) :=
  (freeTensorIso X.sheaf.val (yoneda.obj U₁) (yoneda.obj U₂)).symm ≪≫
    (free (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)).mapIso (yonedaMeetIso U₁ U₂)

end FreeYonedaTensor

end PresheafOfModules
