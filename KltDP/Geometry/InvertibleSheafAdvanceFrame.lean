import KltDP.Geometry.InvertibleSheafSectionAdvance
import KltDP.Geometry.QuasicoherentSectionPowerZero

/-!
# Further powers in actual twist frames

In the original power frames, advancing an existing twisted section by k
factors is multiplication of its original coefficient by the k-th power.
The proved quasicoherent power-zero theorem therefore makes two existing
lifts agree after one common further power on every quasi-compact framed
open. Quasicoherence is required only of the original coefficient module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafAdvanceFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance advanceFrameMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance originalSectionModule {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame
open InvertibleSheafSectionAdvance SchemeModuleTensorScalar ModuleCohomology

private theorem transportedUnit_right_naturality
    {C : Type*} [Category C] [MonoidalCategory C] {O A B : C}
    (e : 𝟙_ C ≅ O) (f : A ⟶ B) :
    (f ⊗ 𝟙 O) ≫ (B ◁ e.inv ≫ (ρ_ B).hom) =
      (A ◁ e.inv ≫ (ρ_ A).hom) ≫ f := by
  rw [tensorHom_id, ← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]

variable {X : Scheme.{u}}

private theorem structureRight_inv_naturality {A B : X.Modules} (f : A ⟶ B) :
    f ≫ (schemeStructureTensorRightIso B).inv =
      (schemeStructureTensorRightIso A).inv ≫
        (f ⊗ 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf)) := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  have h : (f ⊗ 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf)) ≫
      (schemeStructureTensorRightIso B).hom =
      (schemeStructureTensorRightIso A).hom ≫ f :=
    transportedUnit_right_naturality e f
  apply (cancel_mono (schemeStructureTensorRightIso B).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

private theorem framed_step {P Q : X.Modules}
    (f : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ P)
    (g : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ Q)
    (e : P ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (d : Q ≅ _root_.SheafOfModules.unit X.ringCatSheaf) :
    f ≫ (schemeStructureTensorRightIso P).inv ≫ (𝟙 P ⊗ g) ≫
        (e.hom ⊗ d.hom) ≫
        (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom =
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
        ((f ≫ e.hom) ⊗ (g ≫ d.hom)) ≫
        (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom := by
  rw [← tensor_comp_assoc, Category.id_comp]
  rw [← Category.assoc f, structureRight_inv_naturality f, Category.assoc]
  rw [← tensor_comp_assoc, Category.id_comp]

private theorem scalar_one : schemeScalarEnd (1 : Γ(X, ⊤)) =
    𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  apply (_root_.SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  apply (schemeModuleSectionsEquivTop _).injective
  change (schemeScalarEnd (1 : Γ(X, ⊤))).val.app (op ⊤) (1 : Γ(X, ⊤)) =
    (1 : Γ(X, ⊤))
  rw [schemeScalarEnd_appTop, one_mul]

variable (L : InvertibleSheaf X)
  (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (s : L.obj.sections)

/-- The actual advance map has the literal further-power coefficient. -/
theorem advance_frame_conjugate (n k : ℕ) :
    (powerFrame L e n).inv ≫ advance L s n k ≫ (powerFrame L e (n + k)).hom =
      schemeScalarEnd (frameCoefficient L e s ^ k) := by
  induction k with
  | zero =>
    simpa only [advance, Nat.add_zero, Category.id_comp, Iso.inv_hom_id, pow_zero] using
      (scalar_one (X := X)).symm
  | succ k ih =>
    have hf : ((powerFrame L e n).inv ≫ advance L s n k) ≫
        (powerFrame L e (n + k)).hom = schemeScalarEnd (frameCoefficient L e s ^ k) := by
      simpa only [Category.assoc] using ih
    calc
      _ = (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
          ((((powerFrame L e n).inv ≫ advance L s n k) ≫
            (powerFrame L e (n + k)).hom) ⊗ (L.obj.unitHomEquiv.symm s ≫ e.hom)) ≫
          (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom := by
        simpa only [advance, powerFrame, Iso.trans_hom, tensorIso_hom, Category.assoc] using
          framed_step ((powerFrame L e n).inv ≫ advance L s n k)
            (L.obj.unitHomEquiv.symm s) (powerFrame L e (n + k)) e
      _ = _ := by
        rw [hf, sectionHom_frame, schemeStructureTensor_scalar_mul, pow_succ]

/-- The original coefficient-twist frame gives the same literal scalar map. -/
theorem rightAdvance_frame_conjugate (M : X.Modules) (n k : ℕ) :
    (rightTwistFrame M L e n).inv ≫ rightAdvance L s M n k ≫
        (rightTwistFrame M L e (n + k)).hom =
      globalSmulHom M (frameCoefficient L e s ^ k) := by
  calc
    _ = (schemeStructureTensorRightIso M).inv ≫
        (𝟙 M ⊗ ((powerFrame L e n).inv ≫ advance L s n k ≫
          (powerFrame L e (n + k)).hom)) ≫ (schemeStructureTensorRightIso M).hom := by
      simp only [rightTwistFrame, rightAdvance, Iso.trans_inv, Iso.trans_hom,
        tensorIso_inv, tensorIso_hom, Iso.refl_inv, Iso.refl_hom,
        id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    _ = _ := by
      rw [advance_frame_conjugate]
      exact structureTensorRight_scalar_conjugate M (frameCoefficient L e s ^ k)

/-- On every local section, advancing multiplies its original frame coefficient. -/
theorem rightAdvance_frame_apply (M : X.Modules) (n k : ℕ) (V : X.Opens)
    (t : (M ⊗ (power L n).obj).val.obj (op V)) :
    (rightTwistFrame M L e (n + k)).hom.val.app (op V)
        ((rightAdvance L s M n k).val.app (op V) t) =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
          (frameCoefficient L e s ^ k) •
        (rightTwistFrame M L e n).hom.val.app (op V) t := by
  have hh : rightAdvance L s M n k ≫ (rightTwistFrame M L e (n + k)).hom =
      (rightTwistFrame M L e n).hom ≫ globalSmulHom M (frameCoefficient L e s ^ k) := by
    simpa only [Iso.hom_inv_id_assoc] using
      congrArg (fun g : M ⟶ M => (rightTwistFrame M L e n).hom ≫ g)
        (rightAdvance_frame_conjugate L e s M n k)
  have h := congrArg (fun g : M ⊗ (power L n).obj ⟶ M => g.val.app (op V) t) hh
  exact h.trans (globalSmulHom_app M (frameCoefficient L e s ^ k) V
    ((rightTwistFrame M L e n).hom.val.app (op V) t))

/-- Existing twisted sections equal on the coefficient basic open become
equal after all sufficiently many further powers, without a tensor-QC premise. -/
theorem eventually_rightAdvance_eq_of_restrict_eq (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact (U : Set X)) (n : ℕ)
    (t v : (M ⊗ (power L n).obj).val.obj (op U))
    (heq : (M ⊗ (power L n).obj).val.map
        (homOfLE (X.basicOpen_le (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
          (frameCoefficient L e s)))).op t =
      (M ⊗ (power L n).obj).val.map
        (homOfLE (X.basicOpen_le (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
          (frameCoefficient L e s)))).op v) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (rightAdvance L s M n k).val.app (op U) t =
        (rightAdvance L s M n k).val.app (op U) v := by
  let a : Γ(X, U) := X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    (frameCoefficient L e s)
  let ε := rightTwistFrame M L e n
  have heqc : M.val.map (homOfLE (X.basicOpen_le a)).op (ε.hom.val.app (op U) t) =
      M.val.map (homOfLE (X.basicOpen_le a)).op (ε.hom.val.app (op U) v) := by
    rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply, heq]
  obtain ⟨K, hK⟩ := QuasicoherentSectionPowerZero.exists_pow_smul_eq_of_isCompact
    M hU a (ε.hom.val.app (op U) t) (ε.hom.val.app (op U) v) heqc
  refine ⟨K, fun k hk => ?_⟩
  have hpow : a ^ k • ε.hom.val.app (op U) t = a ^ k • ε.hom.val.app (op U) v := by
    have h := congrArg (fun z : M.val.obj (op U) => a ^ (k - K) • z) hK
    simpa only [smul_smul, ← pow_add, Nat.sub_add_cancel hk] using h
  let δ := rightTwistFrame M L e (n + k)
  have ht : δ.hom.val.app (op U) ((rightAdvance L s M n k).val.app (op U) t) =
      a ^ k • ε.hom.val.app (op U) t := by
    simpa only [a, map_pow] using rightAdvance_frame_apply L e s M n k U t
  have hv : δ.hom.val.app (op U) ((rightAdvance L s M n k).val.app (op U) v) =
      a ^ k • ε.hom.val.app (op U) v := by
    simpa only [a, map_pow] using rightAdvance_frame_apply L e s M n k U v
  have hinv (z : (M ⊗ (power L (n + k)).obj).val.obj (op U)) :
      δ.inv.val.app (op U) (δ.hom.val.app (op U) z) = z :=
    congrArg (fun g : M ⊗ (power L (n + k)).obj ⟶ M ⊗ (power L (n + k)).obj =>
      g.val.app (op U) z) δ.hom_inv_id
  exact (hinv _).symm.trans
    ((congrArg (δ.inv.val.app (op U)) (ht.trans (hpow.trans hv.symm))).trans (hinv _))

end KltDP.Geometry.InvertibleSheafAdvanceFrame
