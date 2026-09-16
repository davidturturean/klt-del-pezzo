import KltDP.Geometry.InvertibleSheafSectionPowers
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.RationalTreePicardPulledSectionTransport

/-!
# Original pullback of actual tensor-power sections

The existing pullback tensor and structure-unit isomorphisms compare the
pullback of each constructed tensor power with the power of the original
pullback. The same comparison sends the literal adjunction-unit pullback
of the original power section to the power of the pulled-back section.

This proves the actual restriction comparison needed on chart schemes,
since any scheme morphism is allowed. It does not construct or glue twisted
extensions, or assume an ample sheaf. The multiplication compatibility used
here is the already proved original pullback tensor compatibility.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.InvertibleSheafSectionPowersPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance powerPullbackMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers RationalTreePicard

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Pullback of an actual compatible section family, through the original
structure-unit isomorphism and original pullback functor. -/
def pullbackSection (M : X.Modules) (s : M.sections) :
    ((schemeModulePullback f).obj M).sections :=
  ((schemeModulePullback f).obj M).unitHomEquiv
    ((schemeModulePullbackUnitIso f).inv ≫
      (schemeModulePullback f).map (M.unitHomEquiv.symm s))

/-- This family is the literal adjunction-unit pulled section on every
original inverse-image open. -/
theorem pullbackSection_val (M : X.Modules) (s : M.sections) (U : X.Opens) :
    (pullbackSection f M s).val (op (f ⁻¹ᵁ U)) =
      pulledSection f M U (s.val (op U)) := by
  let α := schemeModulePullbackUnitIso f
  let t := pulledSection f (_root_.SheafOfModules.unit X.ringCatSheaf)
    U (1 : Γ(X, U))
  have ht : α.hom.val.app (op (f ⁻¹ᵁ U)) t = (1 : Γ(Y, f ⁻¹ᵁ U)) := by
    simpa only [map_one] using unitIso_hom_val_app_pulledSection f U (1 : Γ(X, U))
  have hi : α.inv.val.app (op (f ⁻¹ᵁ U)) (1 : Γ(Y, f ⁻¹ᵁ U)) = t := by
    calc
      _ = α.inv.val.app (op (f ⁻¹ᵁ U))
          (α.hom.val.app (op (f ⁻¹ᵁ U)) t) := by rw [ht]
      _ = t := congrArg (fun g :
          (schemeModulePullback f).obj (_root_.SheafOfModules.unit X.ringCatSheaf) ⟶
            (schemeModulePullback f).obj (_root_.SheafOfModules.unit X.ringCatSheaf) =>
          g.val.app (op (f ⁻¹ᵁ U)) t) α.hom_inv_id
  have hs : (M.unitHomEquiv.symm s).val.app (op U) (1 : Γ(X, U)) =
      s.val (op U) :=
    congrArg (fun a : M.sections => a.val (op U)) (M.unitHomEquiv.apply_symm_apply s)
  change ((schemeModulePullback f).map (M.unitHomEquiv.symm s)).val.app
      (op (f ⁻¹ᵁ U)) (α.inv.val.app (op (f ⁻¹ᵁ U)) (1 : Γ(Y, f ⁻¹ᵁ U))) = _
  rw [hi]
  exact (pullback_map_val_app_pulledSection f (M.unitHomEquiv.symm s) U
    (1 : Γ(X, U))).trans (congrArg (pulledSection f M U) hs)

private theorem pullback_structure_inv_tensor :
    (schemeModulePullbackUnitIso f).inv ≫
      (schemeModulePullback f).map
        (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (schemeModulePullbackTensorIso f
        (_root_.SheafOfModules.unit X.ringCatSheaf)
        (_root_.SheafOfModules.unit X.ringCatSheaf)).hom =
    (schemeStructureTensorRightIso (_root_.SheafOfModules.unit Y.ringCatSheaf)).inv ≫
      ((schemeModulePullbackUnitIso f).inv ⊗ (schemeModulePullbackUnitIso f).inv) := by
  let F := schemeModulePullback f
  let α := schemeModulePullbackUnitIso f
  let μX := schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)
  let μY := schemeStructureTensorRightIso (_root_.SheafOfModules.unit Y.ringCatSheaf)
  let δ := schemeModulePullbackTensorIso f
    (_root_.SheafOfModules.unit X.ringCatSheaf)
    (_root_.SheafOfModules.unit X.ringCatSheaf)
  have hmul : δ.hom ≫ (α.hom ⊗ α.hom) ≫ μY.hom = F.map μX.hom ≫ α.hom :=
    schemeModulePullbackTensorIso_structure_mul f
  change α.inv ≫ F.map μX.inv ≫ δ.hom = μY.inv ≫ (α.inv ⊗ α.inv)
  apply (cancel_mono ((α.hom ⊗ α.hom) ≫ μY.hom)).mp
  calc
    _ = α.inv ≫ F.map μX.inv ≫ F.map μX.hom ≫ α.hom := by
      simpa only [Category.assoc] using
        congrArg (fun g => α.inv ≫ F.map μX.inv ≫ g) hmul
    _ = 𝟙 _ := by
      rw [← Functor.map_comp_assoc, μX.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp, α.inv_hom_id]
    _ = _ := by
      simp only [Category.assoc, ← tensor_comp_assoc, Iso.inv_hom_id,
        tensor_id, Category.id_comp]

/-- The original pullback comparison preserves the tensor product of
actual section morphisms, with the original structure-module normalization. -/
theorem pullback_tensor_sectionHom {M N : X.Modules}
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (t : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    (schemeModulePullbackUnitIso f).inv ≫
      (schemeModulePullback f).map
        ((schemeStructureTensorRightIso
          (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫ (s ⊗ t)) ≫
      (schemeModulePullbackTensorIso f M N).hom =
    (schemeStructureTensorRightIso (_root_.SheafOfModules.unit Y.ringCatSheaf)).inv ≫
      (((schemeModulePullbackUnitIso f).inv ≫ (schemeModulePullback f).map s) ⊗
        ((schemeModulePullbackUnitIso f).inv ≫ (schemeModulePullback f).map t)) := by
  calc
    _ = ((schemeModulePullbackUnitIso f).inv ≫
        (schemeModulePullback f).map (schemeStructureTensorRightIso
          (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (schemeModulePullbackTensorIso f
          (_root_.SheafOfModules.unit X.ringCatSheaf)
          (_root_.SheafOfModules.unit X.ringCatSheaf)).hom) ≫
          ((schemeModulePullback f).map s ⊗ (schemeModulePullback f).map t) := by
      simp only [Functor.map_comp, Category.assoc, schemeModulePullbackTensorIso_natural]
    _ = _ := by
      rw [pullback_structure_inv_tensor]
      simp only [tensor_comp, Category.assoc]

/-- The pullback of the actual recursive power is isomorphic to the
actual recursive power of the original pulled-back invertible sheaf. -/
def powerPullbackIso (L : InvertibleSheaf X) : (n : ℕ) →
    (schemeModulePullback f).obj (power L n).obj ≅
      (power (pullbackInvertibleSheaf f L) n).obj
  | 0 => schemeModulePullbackUnitIso f
  | n + 1 => schemeModulePullbackTensorIso f (power L n).obj L.obj ≪≫
    tensorIso (powerPullbackIso L n) (Iso.refl _)

/-- The same isomorphism preserves the original power-section morphism. -/
theorem powerSectionHom_pullback (L : InvertibleSheaf X) (s : L.obj.sections) (n : ℕ) :
    (schemeModulePullbackUnitIso f).inv ≫
      (schemeModulePullback f).map (powerSectionHom L s n) ≫
      (powerPullbackIso f L n).hom =
    powerSectionHom (pullbackInvertibleSheaf f L) (pullbackSection f L.obj s) n := by
  have hs : (pullbackInvertibleSheaf f L).obj.unitHomEquiv.symm
      (pullbackSection f L.obj s) =
      (schemeModulePullbackUnitIso f).inv ≫
        (schemeModulePullback f).map (L.obj.unitHomEquiv.symm s) :=
    (((schemeModulePullback f).obj L.obj).unitHomEquiv).symm_apply_apply _
  induction n with
  | zero =>
    simp only [powerSectionHom, powerPullbackIso, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id]
  | succ n ih =>
    calc
      _ = ((schemeModulePullbackUnitIso f).inv ≫
          (schemeModulePullback f).map
            ((schemeStructureTensorRightIso
              (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
                (powerSectionHom L s n ⊗ L.obj.unitHomEquiv.symm s)) ≫
          (schemeModulePullbackTensorIso f (power L n).obj L.obj).hom) ≫
          ((powerPullbackIso f L n).hom ⊗ 𝟙 ((schemeModulePullback f).obj L.obj)) := by
        simp only [powerSectionHom, powerPullbackIso, Iso.trans_hom, tensorIso_hom,
          Iso.refl_hom, Category.assoc]
      _ = (schemeStructureTensorRightIso
          (_root_.SheafOfModules.unit Y.ringCatSheaf)).inv ≫
          (((schemeModulePullbackUnitIso f).inv ≫
              (schemeModulePullback f).map (powerSectionHom L s n) ≫
              (powerPullbackIso f L n).hom) ⊗
            ((schemeModulePullbackUnitIso f).inv ≫
              (schemeModulePullback f).map (L.obj.unitHomEquiv.symm s))) := by
        rw [pullback_tensor_sectionHom]
        simpa only [Category.assoc, Category.comp_id] using
          congrArg (fun g => (schemeStructureTensorRightIso
            (_root_.SheafOfModules.unit Y.ringCatSheaf)).inv ≫ g)
            (tensor_comp
              ((schemeModulePullbackUnitIso f).inv ≫
                (schemeModulePullback f).map (powerSectionHom L s n))
              ((schemeModulePullbackUnitIso f).inv ≫
                (schemeModulePullback f).map (L.obj.unitHomEquiv.symm s))
              (powerPullbackIso f L n).hom
              (𝟙 ((schemeModulePullback f).obj L.obj))).symm
      _ = _ := by
        rw [ih]
        exact congrArg (fun t : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶
            (pullbackInvertibleSheaf f L).obj =>
          (schemeStructureTensorRightIso
            (_root_.SheafOfModules.unit Y.ringCatSheaf)).inv ≫
            (powerSectionHom (pullbackInvertibleSheaf f L)
              (pullbackSection f L.obj s) n ⊗ t)) hs.symm

/-- On every original open, the comparison sends the literal pulled-back
power section to the power of the literal pulled-back section. -/
theorem powerSection_pullback_val (L : InvertibleSheaf X) (s : L.obj.sections)
    (n : ℕ) (U : X.Opens) :
    (powerPullbackIso f L n).hom.val.app (op (f ⁻¹ᵁ U))
      (pulledSection f (power L n).obj U ((powerSection L s n).val (op U))) =
    (powerSection (pullbackInvertibleSheaf f L) (pullbackSection f L.obj s) n).val
      (op (f ⁻¹ᵁ U)) := by
  have h := congrArg
    (fun g : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶
        (power (pullbackInvertibleSheaf f L) n).obj =>
      g.val.app (op (f ⁻¹ᵁ U)) (1 : Γ(Y, f ⁻¹ᵁ U)))
    (powerSectionHom_pullback f L s n)
  have hp : ((schemeModulePullbackUnitIso f).inv ≫
      (schemeModulePullback f).map (powerSectionHom L s n)).val.app
        (op (f ⁻¹ᵁ U)) (1 : Γ(Y, f ⁻¹ᵁ U)) =
      pulledSection f (power L n).obj U ((powerSection L s n).val (op U)) := by
    simpa only [pullbackSection, powerSection, Equiv.symm_apply_apply] using
      pullbackSection_val f (power L n).obj (powerSection L s n) U
  change (powerPullbackIso f L n).hom.val.app (op (f ⁻¹ᵁ U))
      (((schemeModulePullbackUnitIso f).inv ≫
        (schemeModulePullback f).map (powerSectionHom L s n)).val.app
          (op (f ⁻¹ᵁ U)) (1 : Γ(Y, f ⁻¹ᵁ U))) = _ at h
  rw [hp] at h
  exact h

end KltDP.Geometry.InvertibleSheafSectionPowersPullback
