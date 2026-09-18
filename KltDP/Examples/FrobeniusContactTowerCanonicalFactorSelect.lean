import KltDP.Examples.FrobeniusContactTowerCanonicalFactorUnits

/-!
# Selecting the remaining actual factor on a cluster open

When every other original inclusion is invertible, remove those factors by
those inclusions and the original structure-module unitors. The resulting
isomorphism preserves the entire original product inclusion. This is finite
recursion of the previously defined actual family tensor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorSelect

open KltDP.Geometry FrobeniusContactTowerCanonicalFactorTensor
open FrobeniusContactTowerCanonicalFactorFiniteTensor FrobeniusContactTowerCanonicalFactorUnits

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance factorSelectModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Multiplication by the actual left unit retains the original remaining inclusion. -/
theorem productInclusion_left_unit {X : Scheme.{u}} {J : X.Modules}
    (j : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    productInclusion (𝟙 _) j = (schemeStructureTensorLeftIso J).hom ≫ j := by
  simp only [productInclusion, schemeStructureTensorInclusion_eq, tensorHom_id,
    id_whiskerRight, Category.id_comp]

/-- Removing an actual invertible left factor preserves the same product map. -/
theorem tensorLeftUnit_comp {X : Scheme.{u}} {I M J : X.Modules}
    (v : I ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (e : M ≅ J)
    (j : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (tensorIso v e).hom ≫ (schemeStructureTensorLeftIso J).hom ≫ j =
      productInclusion v.hom (e.hom ≫ j) := by
  rw [← productInclusion_left_unit, tensorIso_productInclusion, Category.comp_id]

/-- Remove precisely the other factors through their actual invertible inclusions. -/
def familySelectIso {X : Scheme.{u}} : (n : ℕ) → (L : Fin n → InvertibleSheaf X) →
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) →
    (r : Fin n) → (∀ s, s ≠ r → IsIso (i s)) →
    ((familyLine n L).obj ≅ (L r).obj)
  | 0, _, _, r, _ => Fin.elim0 r
  | n + 1, L, i, r, h => by
      cases r using Fin.lastCases with
      | last =>
          letI : IsIso (familyInclusion n (fun s => L s.castSucc)
              (fun s => i s.castSucc)) :=
            familyInclusion_isIso n _ _ (fun s => h s.castSucc s.castSucc_ne_last)
          exact tensorIso
              (asIso (familyInclusion n (fun s => L s.castSucc) (fun s => i s.castSucc)))
              (Iso.refl (L (Fin.last n)).obj) ≪≫
            schemeStructureTensorLeftIso (L (Fin.last n)).obj
      | cast r =>
          letI : IsIso (i (Fin.last n)) := h (Fin.last n) r.castSucc_ne_last.symm
          exact tensorIso
              (familySelectIso n (fun s => L s.castSucc) (fun s => i s.castSucc) r
                (fun s hs => h s.castSucc (fun he => hs (Fin.castSucc_injective n he))))
              (asIso (i (Fin.last n))) ≪≫
            schemeStructureTensorRightIso (L r.castSucc).obj

/-- The selected factor still has exactly the original full family inclusion. -/
theorem familySelectIso_inclusion {X : Scheme.{u}} (n : ℕ)
    (L : Fin n → InvertibleSheaf X)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (r : Fin n) (h : ∀ s, s ≠ r → IsIso (i s)) :
    (familySelectIso n L i r h).hom ≫ i r = familyInclusion n L i := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      cases r using Fin.lastCases with
      | last =>
          letI : IsIso (familyInclusion n (fun s => L s.castSucc)
              (fun s => i s.castSucc)) :=
            familyInclusion_isIso n _ _ (fun s => h s.castSucc s.castSucc_ne_last)
          simp only [familySelectIso, Fin.lastCases_last, Fin.lastCases_castSucc,
            Iso.trans_hom, Category.assoc]
          change (tensorIso
              (asIso (familyInclusion n (fun s => L s.castSucc) (fun s => i s.castSucc)))
              (Iso.refl (L (Fin.last n)).obj)).hom ≫
            (schemeStructureTensorLeftIso (L (Fin.last n)).obj).hom ≫ i (Fin.last n) =
            productInclusion
              (familyInclusion n (fun s => L s.castSucc) (fun s => i s.castSucc))
              (i (Fin.last n))
          rw [tensorLeftUnit_comp]
          simp only [asIso_hom, Iso.refl_hom, Category.id_comp]
      | cast r =>
          letI : IsIso (i (Fin.last n)) := h (Fin.last n) r.castSucc_ne_last.symm
          simp only [familySelectIso, Fin.lastCases_last, Fin.lastCases_castSucc,
            Iso.trans_hom, Category.assoc]
          change (tensorIso
              (familySelectIso n (fun s => L s.castSucc) (fun s => i s.castSucc) r
                (fun s hs => h s.castSucc (fun he => hs (Fin.castSucc_injective n he))))
              (asIso (i (Fin.last n)))).hom ≫
            (schemeStructureTensorRightIso (L r.castSucc).obj).hom ≫ i r.castSucc =
            productInclusion
              (familyInclusion n (fun s => L s.castSucc) (fun s => i s.castSucc))
              (i (Fin.last n))
          rw [tensorRightUnit_comp, asIso_hom, ih]

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorSelect
