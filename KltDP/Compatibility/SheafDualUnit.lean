/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

Adapted from CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/Dual.lean, dualUnitSectionsEquiv
and its two evaluation formulas (upstream lines 501–523).
-/
import KltDP.Compatibility.SheafDual

/-!
# Local endomorphisms of the actual unit sheaf

Evaluation at one identifies unit endomorphisms on the over-site with
sections of the original ring sheaf. This is a bijection of actual maps.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace KltDP.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- An endomorphism of the unit module over `Over U` is determined by its value at
`1` over the terminal object. -/
noncomputable def dualUnitSectionsEquiv (U : C) :
    (_root_.SheafOfModules.unit (R.over U) ⟶
      _root_.SheafOfModules.unit (R.over U)) ≃ R.val.obj (op U) :=
  (_root_.SheafOfModules.unit (R.over U)).unitHomEquiv.trans
    (overUnitSectionEquiv R U).symm

@[simp]
theorem dualUnitSectionsEquiv_apply (U : C)
    (α : _root_.SheafOfModules.unit (R.over U) ⟶
      _root_.SheafOfModules.unit (R.over U)) :
    dualUnitSectionsEquiv R U α =
      α.val.app (op (Over.mk (𝟙 U)))
        (show (R.over U).val.obj (op (Over.mk (𝟙 U))) from 1) :=
  rfl

@[simp]
theorem dualUnitSectionsEquiv_symm_apply (U : C) (r : R.val.obj (op U)) :
    (dualUnitSectionsEquiv R U).symm r = overUnitScalarEnd R U r :=
  rfl

end KltDP.SheafOfModules
