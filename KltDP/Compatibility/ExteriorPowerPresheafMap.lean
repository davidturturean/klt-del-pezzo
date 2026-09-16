import KltDP.Compatibility.ExteriorPowerPresheaf

/-!
# Maps of the original exterior-power presheaves

The pointwise map is the pinned `ModuleCat.exteriorPower.map`. Its naturality
uses the original module-presheaf morphism and the existing semilinear
restriction maps, checked on pure wedges. No frame or replacement module is
part of the construction.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace KltDP.Compatibility.ExteriorPowerPresheaf

variable {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ CommRingCat.{u})
  {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

local instance mapRingObjCommRing (V : Cᵒᵖ) :
    CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj V) :=
  inferInstanceAs (CommRing (R.obj V))

/-- An original module-presheaf morphism induces a morphism between the
existing exterior-power presheaves. -/
def map (f : M ⟶ N) (n : ℕ) : presheaf R M n ⟶ presheaf R N n where
  app V := ModuleCat.exteriorPower.map (f.app V) n
  naturality {V W} g := by
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro m
    change ModuleCat.exteriorPower.map (f.app W) n
        (restriction R M n g (ModuleCat.exteriorPower.mk m)) =
      restriction R N n g
        (ModuleCat.exteriorPower.map (f.app V) n (ModuleCat.exteriorPower.mk m))
    rw [restriction_mk, ModuleCat.exteriorPower.map_mk,
      ModuleCat.exteriorPower.map_mk, restriction_mk]
    congr 1
    funext i
    exact _root_.PresheafOfModules.naturality_apply f g (m i)

/-- On a pure wedge, the new presheaf morphism applies the original map to
every factor. -/
@[simp]
theorem map_mk (f : M ⟶ N) (n : ℕ) (V : Cᵒᵖ) (m : Fin n → M.obj V) :
    (map R f n).app V (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := N.obj V) (fun i => f.app V (m i)) :=
  ModuleCat.exteriorPower.map_mk (f.app V) m

@[simp]
theorem map_id (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (n : ℕ) : map R (𝟙 M) n = 𝟙 (presheaf R M n) := by
  apply _root_.PresheafOfModules.hom_ext
  intro V
  change ModuleCat.exteriorPower.map (𝟙 (M.obj V)) n =
    𝟙 ((M.obj V).exteriorPower n)
  exact (ModuleCat.exteriorPower.functor (R.obj V) n).map_id (M.obj V)

@[simp]
theorem map_comp (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    map R (f ≫ g) n = map R f n ≫ map R g n := by
  apply _root_.PresheafOfModules.hom_ext
  intro V
  change ModuleCat.exteriorPower.map (f.app V ≫ g.app V) n =
    ModuleCat.exteriorPower.map (f.app V) n ≫ ModuleCat.exteriorPower.map (g.app V) n
  exact (ModuleCat.exteriorPower.functor (R.obj V) n).map_comp (f.app V) (g.app V)

end KltDP.Compatibility.ExteriorPowerPresheaf
