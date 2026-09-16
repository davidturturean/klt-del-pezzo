import KltDP.Geometry.SchemeModulePullbackStructureRight
import KltDP.Geometry.InvertibleSheafPowerFramePullback
import KltDP.Geometry.InvertibleSheafTwistFrame

/-!
# Original power twists and their frames under pullback

The actual pullback of `M tensor L^n` is compared with `f^*M tensor (f^*L)^n`
using the original tensor comparison and the constructed power comparison.
It carries the original multiplication-by-section map to the corresponding
map for the literally pulled section. In an actual frame it also commutes
with the original coefficient map, including its formula on every original
pulled local section.

These transport equations have no quasicoherence or monoidal-compatibility
hypothesis. They are prerequisites for gluing local twisted extensions;
that gluing and a Serre-ample witness remain separate constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.InvertibleSheafTwistPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance twistPullbackMonoidal (Z : Scheme.{u}) : MonoidalCategory Z.Modules :=
  Scheme.Modules.monoidalCategory Z

open InvertibleSheafSectionPowers InvertibleSheafSectionPowersPullback
open InvertibleSheafPowerFramePullback InvertibleSheafTwistFrame
open SchemeModulePullbackStructureRight RationalTreePicard

private theorem tensor_id_two {C : Type*} [Category C] [MonoidalCategory C]
    (A : C) {B D E W Z : C} (u : W ⟶ A ⊗ B)
    (a : B ⟶ D) (b : D ⟶ E) (v : A ⊗ E ⟶ Z) :
    u ≫ (𝟙 A ⊗ a) ≫ (𝟙 A ⊗ b) ≫ v = u ≫ (𝟙 A ⊗ (a ≫ b)) ≫ v := by
  simp only [id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc]

private theorem tensor_id_three {C : Type*} [Category C] [MonoidalCategory C]
    (A : C) {B D E W Z : C} (u : W ⟶ A ⊗ B)
    (a : B ⟶ D) (b : D ⟶ E) (c : E ⟶ Z) :
    u ≫ (𝟙 A ⊗ a) ≫ (𝟙 A ⊗ b) ≫ (𝟙 A ⊗ c) =
      u ≫ (𝟙 A ⊗ (a ≫ b ≫ c)) := by
  simp only [id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc]

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (L : InvertibleSheaf X)

/-- The original tensor and power comparisons on the actual coefficient twist. -/
def twistPullbackIso (n : ℕ) :
    (schemeModulePullback f).obj (M ⊗ (power L n).obj) ≅
      (schemeModulePullback f).obj M ⊗ (power (pullbackInvertibleSheaf f L) n).obj :=
  schemeModulePullbackTensorIso f M (power L n).obj ≪≫
    tensorIso (Iso.refl ((schemeModulePullback f).obj M)) (powerPullbackIso f L n)

private theorem pullback_structure_right_inv :
    (schemeModulePullback f).map (schemeStructureTensorRightIso M).inv ≫
      (schemeModulePullbackTensorIso f M (_root_.SheafOfModules.unit X.ringCatSheaf)).hom =
    (schemeStructureTensorRightIso ((schemeModulePullback f).obj M)).inv ≫
      (𝟙 ((schemeModulePullback f).obj M) ⊗ (schemeModulePullbackUnitIso f).inv) := by
  let F := schemeModulePullback f
  let α := schemeModulePullbackUnitIso f
  let uX := schemeStructureTensorRightIso M
  let uY := schemeStructureTensorRightIso (F.obj M)
  let δ := schemeModulePullbackTensorIso f M (_root_.SheafOfModules.unit X.ringCatSheaf)
  have hu : δ.hom ≫ (𝟙 (F.obj M) ⊗ α.hom) ≫ uY.hom = F.map uX.hom :=
    pullbackTensor_structure_right f M
  change F.map uX.inv ≫ δ.hom = uY.inv ≫ (𝟙 (F.obj M) ⊗ α.inv)
  apply (cancel_mono ((𝟙 (F.obj M) ⊗ α.hom) ≫ uY.hom)).mp
  calc
    _ = F.map uX.inv ≫ F.map uX.hom := by
      simpa only [Category.assoc] using congrArg (fun g => F.map uX.inv ≫ g) hu
    _ = 𝟙 _ := by
      rw [← Functor.map_comp, uX.inv_hom_id, CategoryTheory.Functor.map_id]
    _ = _ := by
      simp only [Category.assoc, ← tensor_comp_assoc, Iso.inv_hom_id,
        Category.id_comp, tensor_id]

set_option maxHeartbeats 800000 in
/-- The original tensor twist map pulls back to the twist map formed
from the literal adjunction-unit pullback of the original section. -/
theorem rightTwistMap_pullback (s : L.obj.sections) (n : ℕ) :
    (schemeModulePullback f).map (rightTwistMap M L s n) ≫
        (twistPullbackIso f M L n).hom =
      rightTwistMap ((schemeModulePullback f).obj M) (pullbackInvertibleSheaf f L)
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n := by
  let F := schemeModulePullback f
  let α := schemeModulePullbackUnitIso f
  let uX := schemeStructureTensorRightIso M
  let uY := schemeStructureTensorRightIso (F.obj M)
  let δ := schemeModulePullbackTensorIso f M (_root_.SheafOfModules.unit X.ringCatSheaf)
  let σ := powerSectionHom L s n
  let E := powerPullbackIso f L n
  have hn := schemeModulePullbackTensorIso_natural f (𝟙 M) σ
  have hi : F.map uX.inv ≫ δ.hom = uY.inv ≫ (𝟙 (F.obj M) ⊗ α.inv) :=
    pullback_structure_right_inv f M
  have hs : α.inv ≫ F.map σ ≫ E.hom =
      powerSectionHom (pullbackInvertibleSheaf f L) (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n :=
    powerSectionHom_pullback f L s n
  calc
    _ = (F.map uX.inv ≫ δ.hom) ≫
        (𝟙 (F.obj M) ⊗ F.map σ) ≫ (𝟙 (F.obj M) ⊗ E.hom) := by
      simpa only [rightTwistMap, twistPullbackIso, Iso.trans_hom, tensorIso_hom,
        Iso.refl_hom, Functor.map_comp, Category.assoc, CategoryTheory.Functor.map_id] using
        congrArg (fun g => F.map uX.inv ≫ g ≫ (𝟙 (F.obj M) ⊗ E.hom)) hn
    _ = uY.inv ≫ (𝟙 (F.obj M) ⊗ (α.inv ≫ F.map σ ≫ E.hom)) := by
      rw [hi]
      simpa only [Category.assoc] using
        tensor_id_three (F.obj M) uY.inv α.inv (F.map σ) E.hom
    _ = _ := by
      rw [hs]
      rfl

set_option maxHeartbeats 800000 in
/-- The actual pullback comparison commutes with the original power-twist
frame of every actual coefficient module. -/
theorem rightTwistFrame_pullback
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (n : ℕ) :
    (twistPullbackIso f M L n).hom ≫
        (rightTwistFrame ((schemeModulePullback f).obj M) (pullbackInvertibleSheaf f L)
          (pullbackFrame f L e) n).hom =
      (schemeModulePullback f).map (rightTwistFrame M L e n).hom := by
  let F := schemeModulePullback f
  let α := schemeModulePullbackUnitIso f
  let pX := powerFrame L e n
  let pY := powerFrame (pullbackInvertibleSheaf f L) (pullbackFrame f L e) n
  let E := powerPullbackIso f L n
  let δ := schemeModulePullbackTensorIso f M (power L n).obj
  let uY := schemeStructureTensorRightIso (F.obj M)
  have hp : E.hom ≫ pY.hom = F.map pX.hom ≫ α.hom := powerFrame_pullback f L e n
  have hn : δ.hom ≫ (𝟙 (F.obj M) ⊗ F.map pX.hom) =
      F.map (𝟙 M ⊗ pX.hom) ≫
        (schemeModulePullbackTensorIso f M (_root_.SheafOfModules.unit X.ringCatSheaf)).hom := by
    simpa only [CategoryTheory.Functor.map_id] using
      (schemeModulePullbackTensorIso_natural f (𝟙 M) pX.hom).symm
  calc
    _ = δ.hom ≫ (𝟙 (F.obj M) ⊗ (E.hom ≫ pY.hom)) ≫ uY.hom := by
      change δ.hom ≫ (𝟙 (F.obj M) ⊗ E.hom) ≫
        (𝟙 (F.obj M) ⊗ pY.hom) ≫ uY.hom = _
      exact tensor_id_two (F.obj M) δ.hom E.hom pY.hom uY.hom
    _ = δ.hom ≫ (𝟙 (F.obj M) ⊗ F.map pX.hom) ≫
        (𝟙 (F.obj M) ⊗ α.hom) ≫ uY.hom := by
      rw [hp]
      exact (tensor_id_two (F.obj M) δ.hom (F.map pX.hom) α.hom uY.hom).symm
    _ = F.map (𝟙 M ⊗ pX.hom) ≫
        (schemeModulePullbackTensorIso f M (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫
        (𝟙 (F.obj M) ⊗ α.hom) ≫ uY.hom := by
      simpa only [Category.assoc] using
        congrArg (fun g => g ≫ (𝟙 (F.obj M) ⊗ α.hom) ≫ uY.hom) hn
    _ = _ := by
      rw [pullbackTensor_structure_right]
      simp only [rightTwistFrame, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
        Functor.map_comp]
      rfl

/-- On every original pulled local section, the pulled twist coefficient
is literally the pullback of its original coefficient. -/
theorem rightTwistFrame_pulledSection
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (n : ℕ)
    (V : X.Opens) (t : (M ⊗ (power L n).obj).val.obj (op V)) :
    (rightTwistFrame ((schemeModulePullback f).obj M) (pullbackInvertibleSheaf f L)
        (pullbackFrame f L e) n).hom.val.app (op (f ⁻¹ᵁ V))
      ((twistPullbackIso f M L n).hom.val.app (op (f ⁻¹ᵁ V))
        (pulledSection f (M ⊗ (power L n).obj) V t)) =
    pulledSection f M V ((rightTwistFrame M L e n).hom.val.app (op V) t) := by
  have h := congrArg (fun g : (schemeModulePullback f).obj (M ⊗ (power L n).obj) ⟶
      (schemeModulePullback f).obj M =>
      g.val.app (op (f ⁻¹ᵁ V)) (pulledSection f (M ⊗ (power L n).obj) V t))
    (rightTwistFrame_pullback f M L e n)
  exact h.trans (pullback_map_val_app_pulledSection f (rightTwistFrame M L e n).hom V t)

end KltDP.Geometry.InvertibleSheafTwistPullback
