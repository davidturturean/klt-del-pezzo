import KltDP.Geometry.InvertibleSheafSectionAdvance
import KltDP.Geometry.InvertibleSheafOpenTwistSections

/-!
# Further-power maps on original open charts

The recursive further-power map commutes with the already constructed
actual pullback tensor and power comparisons. For an open immersion this
identifies its action on chart sections with its action on the original
ambient twisted sections. This is the transport needed for overlap equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafAdvancePullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance advancePullbackMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers InvertibleSheafSectionPowersPullback
open InvertibleSheafSectionAdvance InvertibleSheafTwistPullback
open InvertibleSheafOpenTwistSections SchemeModuleOpenPullbackSections
open SchemeModulePullbackStructureRight

private theorem tensor_exchange_after {C : Type*} [Category C] [MonoidalCategory C]
    {O A B D W : C} (u : W ⟶ A ⊗ O) (g : A ⟶ B) (a : O ⟶ D) :
    u ≫ (𝟙 A ⊗ a) ≫ (g ⊗ 𝟙 D) = u ≫ (g ⊗ 𝟙 O) ≫ (𝟙 B ⊗ a) := by
  simp only [id_tensorHom, tensorHom_id, whisker_exchange]

private theorem tensor_id_comp_after {C : Type*} [Category C] [MonoidalCategory C]
    (A : C) {B D E W : C} (u : W ⟶ A ⊗ B) (a : B ⟶ D) (b : D ⟶ E) :
    u ≫ (𝟙 A ⊗ a) ≫ (𝟙 A ⊗ b) = u ≫ (𝟙 A ⊗ (a ≫ b)) := by
  simp only [id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc]

private theorem transportedUnit_right_naturality
    {C : Type*} [Category C] [MonoidalCategory C] {O A B : C}
    (e : 𝟙_ C ≅ O) (g : A ⟶ B) :
    (g ⊗ 𝟙 O) ≫ (B ◁ e.inv ≫ (ρ_ B).hom) =
      (A ◁ e.inv ≫ (ρ_ A).hom) ≫ g := by
  rw [tensorHom_id, ← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]

private theorem structureRight_inv_naturality {X : Scheme.{u}} {A B : X.Modules}
    (g : A ⟶ B) :
    g ≫ (schemeStructureTensorRightIso B).inv =
      (schemeStructureTensorRightIso A).inv ≫
        (g ⊗ 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf)) := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  have h : (g ⊗ 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf)) ≫
      (schemeStructureTensorRightIso B).hom =
      (schemeStructureTensorRightIso A).hom ≫ g :=
    transportedUnit_right_naturality e g
  apply (cancel_mono (schemeStructureTensorRightIso B).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

private theorem append_naturality {X : Scheme.{u}} {A B C : X.Modules}
    (g : A ⟶ B) (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ C) :
    (schemeStructureTensorRightIso A).inv ≫ (𝟙 A ⊗ s) ≫ (g ⊗ 𝟙 C) =
      g ≫ (schemeStructureTensorRightIso B).inv ≫ (𝟙 B ⊗ s) := by
  rw [← Category.assoc g, structureRight_inv_naturality g, Category.assoc]
  exact tensor_exchange_after (schemeStructureTensorRightIso A).inv g s

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

private theorem pullback_structure_right_inv (M : X.Modules) :
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

private theorem append_pullback (M N : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    (schemeModulePullback f).map ((schemeStructureTensorRightIso M).inv ≫ (𝟙 M ⊗ s)) ≫
        (schemeModulePullbackTensorIso f M N).hom =
      (schemeStructureTensorRightIso ((schemeModulePullback f).obj M)).inv ≫
        (𝟙 ((schemeModulePullback f).obj M) ⊗
          ((schemeModulePullbackUnitIso f).inv ≫ (schemeModulePullback f).map s)) := by
  let F := schemeModulePullback f
  calc
    _ = F.map (schemeStructureTensorRightIso M).inv ≫
        (schemeModulePullbackTensorIso f M (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫
        (𝟙 (F.obj M) ⊗ F.map s) := by
      simpa only [Functor.map_comp, Category.assoc, CategoryTheory.Functor.map_id] using
        congrArg (fun g => F.map (schemeStructureTensorRightIso M).inv ≫ g)
          (schemeModulePullbackTensorIso_natural f (𝟙 M) s)
    _ = (schemeStructureTensorRightIso (F.obj M)).inv ≫
        (𝟙 (F.obj M) ⊗ (schemeModulePullbackUnitIso f).inv) ≫
        (𝟙 (F.obj M) ⊗ F.map s) := by
      simpa only [F, Category.assoc] using
        congrArg (fun g => g ≫ (𝟙 (F.obj M) ⊗ F.map s))
          (pullback_structure_right_inv f M)
    _ = _ := tensor_id_comp_after (F.obj M)
      (schemeStructureTensorRightIso (F.obj M)).inv (schemeModulePullbackUnitIso f).inv (F.map s)

variable (L : InvertibleSheaf X) (s : L.obj.sections)

/-- The actual recursive advance map commutes with the actual power pullback. -/
theorem advance_pullback (n k : ℕ) :
    (schemeModulePullback f).map (advance L s n k) ≫ (powerPullbackIso f L (n + k)).hom =
      (powerPullbackIso f L n).hom ≫
        advance (pullbackInvertibleSheaf f L)
          (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n k := by
  let F := schemeModulePullback f
  let LY := pullbackInvertibleSheaf f L
  let sY := InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s
  have hs : LY.obj.unitHomEquiv.symm sY =
      (schemeModulePullbackUnitIso f).inv ≫ F.map (L.obj.unitHomEquiv.symm s) :=
    (((schemeModulePullback f).obj L.obj).unitHomEquiv).symm_apply_apply _
  induction k with
  | zero => simp only [advance, Nat.add_zero, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id]
  | succ k ih =>
    calc
      _ = F.map (advance L s n k) ≫
          (schemeStructureTensorRightIso (F.obj (power L (n + k)).obj)).inv ≫
          (𝟙 (F.obj (power L (n + k)).obj) ⊗ LY.obj.unitHomEquiv.symm sY) ≫
          ((powerPullbackIso f L (n + k)).hom ⊗ 𝟙 (F.obj L.obj)) := by
        have h := congrArg (fun g => F.map (advance L s n k) ≫ g ≫
            ((powerPullbackIso f L (n + k)).hom ⊗ 𝟙 (F.obj L.obj)))
          (append_pullback f (power L (n + k)).obj L.obj (L.obj.unitHomEquiv.symm s))
        rw [← hs] at h
        simpa only [advance, powerPullbackIso, Iso.trans_hom, tensorIso_hom,
          Iso.refl_hom, Functor.map_comp, Category.assoc] using h
      _ = F.map (advance L s n k) ≫ (powerPullbackIso f L (n + k)).hom ≫
          (schemeStructureTensorRightIso (power LY (n + k)).obj).inv ≫
          (𝟙 (power LY (n + k)).obj ⊗ LY.obj.unitHomEquiv.symm sY) := by
        simpa only [Category.assoc] using
          congrArg (fun g => F.map (advance L s n k) ≫ g)
            (append_naturality (powerPullbackIso f L (n + k)).hom (LY.obj.unitHomEquiv.symm sY))
      _ = _ := by
        rw [← Category.assoc (F.map (advance L s n k)), ih]
        rfl

/-- The actual original coefficient advance commutes with the actual twist comparison. -/
theorem rightAdvance_pullback (M : X.Modules) (n k : ℕ) :
    (schemeModulePullback f).map (rightAdvance L s M n k) ≫
        (twistPullbackIso f M L (n + k)).hom =
      (twistPullbackIso f M L n).hom ≫
        rightAdvance (pullbackInvertibleSheaf f L)
          (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s)
          ((schemeModulePullback f).obj M) n k := by
  let F := schemeModulePullback f
  calc
    _ = (schemeModulePullbackTensorIso f M (power L n).obj).hom ≫
        (𝟙 (F.obj M) ⊗ F.map (advance L s n k)) ≫
        (𝟙 (F.obj M) ⊗ (powerPullbackIso f L (n + k)).hom) := by
      have h := congrArg (fun g => g ≫ (𝟙 (F.obj M) ⊗
          (powerPullbackIso f L (n + k)).hom))
        (schemeModulePullbackTensorIso_natural f (𝟙 M) (advance L s n k))
      simpa only [rightAdvance, twistPullbackIso, Iso.trans_hom, tensorIso_hom,
        Iso.refl_hom, CategoryTheory.Functor.map_id, Category.assoc] using h
    _ = (schemeModulePullbackTensorIso f M (power L n).obj).hom ≫
        (𝟙 (F.obj M) ⊗ (F.map (advance L s n k) ≫
          (powerPullbackIso f L (n + k)).hom)) :=
      tensor_id_comp_after (F.obj M) (schemeModulePullbackTensorIso f M (power L n).obj).hom
        (F.map (advance L s n k)) (powerPullbackIso f L (n + k)).hom
    _ = _ := by
      rw [advance_pullback]
      change (schemeModulePullbackTensorIso f M (power L n).obj).hom ≫
          (𝟙 (F.obj M) ⊗ ((powerPullbackIso f L n).hom ≫
            advance (pullbackInvertibleSheaf f L)
              (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n k)) =
        (schemeModulePullbackTensorIso f M (power L n).obj).hom ≫
          (𝟙 (F.obj M) ⊗ (powerPullbackIso f L n).hom) ≫
          (𝟙 (F.obj M) ⊗ advance (pullbackInvertibleSheaf f L)
            (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n k)
      exact (tensor_id_comp_after (F.obj M) (schemeModulePullbackTensorIso f M (power L n).obj).hom
        (powerPullbackIso f L n).hom (advance (pullbackInvertibleSheaf f L)
          (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) n k)).symm

/-- For an actual open chart, the section equivalence transports the actual
further-power map back to the original ambient further-power map. -/
theorem twistSectionsEquiv_rightAdvance [IsOpenImmersion f] (M : X.Modules)
    (n k : ℕ) (V : Y.Opens) (W : X.Opens) (h : f ''ᵁ V = W)
    (t : ((schemeModulePullback f).obj M ⊗
      (power (pullbackInvertibleSheaf f L) n).obj).val.obj (op V)) :
    twistSectionsEquiv f M L (n + k) V W h
        ((rightAdvance (pullbackInvertibleSheaf f L)
          (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s)
          ((schemeModulePullback f).obj M) n k).val.app (op V) t) =
      (rightAdvance L s M n k).val.app (op W) (twistSectionsEquiv f M L n V W h t) := by
  let E := twistPullbackIso f M L n
  let E' := twistPullbackIso f M L (n + k)
  let g := rightAdvance L s M n k
  let gY := rightAdvance (pullbackInvertibleSheaf f L)
    (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s)
    ((schemeModulePullback f).obj M) n k
  have hg : gY ≫ E'.inv = E.inv ≫ (schemeModulePullback f).map g := by
    have h₀ : (schemeModulePullback f).map g ≫ E'.hom = E.hom ≫ gY :=
      rightAdvance_pullback f L s M n k
    have hh := congrArg (fun q => E.inv ≫ q ≫ E'.inv)
      h₀
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using hh.symm
  have hs := congrArg (fun q => q.val.app (op V) t) hg
  calc
    _ = sectionsEquiv f (M ⊗ (power L (n + k)).obj) V W h
        (((schemeModulePullback f).map g).val.app (op V) (E.inv.val.app (op V) t)) :=
      congrArg (sectionsEquiv f (M ⊗ (power L (n + k)).obj) V W h) hs
    _ = _ := sectionsEquiv_map f (M ⊗ (power L n).obj) g V W h (E.inv.val.app (op V) t)

end KltDP.Geometry.InvertibleSheafAdvancePullback
