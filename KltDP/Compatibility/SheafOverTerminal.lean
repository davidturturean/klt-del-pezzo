import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Recovering module sheaves from restriction over a terminal object

The pinned `CategoryTheory.Over.equivalenceOfIsTerminal` identifies the
over-category of a terminal object with the original category. This adapter
uses its canonical objects `U ⟶ T` to recover actual module-sheaf morphisms
and isomorphisms from their restrictions. It reuses the pinned `over`,
module-sheaf morphisms and their naturality; no sheafification, descent
assumption or additional sheaf condition is introduced.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u₁ v₁

namespace KltDP.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (T : C) (hT : IsTerminal T)

/-- A morphism over a terminal object gives an actual global morphism by
evaluation at the canonical structure arrows to that object. -/
def homFromOverTerminal {M N : _root_.SheafOfModules.{v} R}
    (φ : M.over T ⟶ N.over T) : M ⟶ N where
  val :=
    { app U := φ.val.app (op (Over.mk (hT.from U.unop)))
      naturality := fun {U V} f ↦
        φ.val.naturality
          (Over.homMk f.unop (hT.hom_ext _ _) :
            Over.mk (hT.from V.unop) ⟶ Over.mk (hT.from U.unop)).op }

@[simp]
theorem homFromOverTerminal_app {M N : _root_.SheafOfModules.{v} R}
    (φ : M.over T ⟶ N.over T) (U : Cᵒᵖ) :
    (homFromOverTerminal R T hT φ).val.app U =
      φ.val.app (op (Over.mk (hT.from U.unop))) := rfl

@[simp]
theorem homFromOverTerminal_id (M : _root_.SheafOfModules.{v} R) :
    homFromOverTerminal R T hT (𝟙 (M.over T)) = 𝟙 M := rfl

@[simp]
theorem homFromOverTerminal_comp {M N P : _root_.SheafOfModules.{v} R}
    (φ : M.over T ⟶ N.over T) (ψ : N.over T ⟶ P.over T) :
    homFromOverTerminal R T hT (φ ≫ ψ) =
      homFromOverTerminal R T hT φ ≫ homFromOverTerminal R T hT ψ := rfl

/-- An isomorphism after restriction over a terminal object is an actual
isomorphism of the original module sheaves. -/
def isoFromOverTerminal {M N : _root_.SheafOfModules.{v} R}
    (e : M.over T ≅ N.over T) : M ≅ N where
  hom := homFromOverTerminal R T hT e.hom
  inv := homFromOverTerminal R T hT e.inv
  hom_inv_id := by
    rw [← homFromOverTerminal_comp, e.hom_inv_id, homFromOverTerminal_id]
  inv_hom_id := by
    rw [← homFromOverTerminal_comp, e.inv_hom_id, homFromOverTerminal_id]

@[simp]
theorem isoFromOverTerminal_hom_app {M N : _root_.SheafOfModules.{v} R}
    (e : M.over T ≅ N.over T) (U : Cᵒᵖ) :
    (isoFromOverTerminal R T hT e).hom.val.app U =
      e.hom.val.app (op (Over.mk (hT.from U.unop))) := rfl

@[simp]
theorem isoFromOverTerminal_inv_app {M N : _root_.SheafOfModules.{v} R}
    (e : M.over T ≅ N.over T) (U : Cᵒᵖ) :
    (isoFromOverTerminal R T hT e).inv.val.app U =
      e.inv.val.app (op (Over.mk (hT.from U.unop))) := rfl

end KltDP.SheafOfModules
