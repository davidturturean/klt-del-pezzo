/-
Copyright (c) 2026 Vasily Ilin, Codex. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex

The sectionwise coefficient-action proofs adapt the original
ModuleCohomology.lean multiplication laws (Apache 2.0).
-/
import KltDP.Geometry.BaseRingDerivedComparison

/-!
# Original scalar action on derived abelian global sections

The coefficient ring acts on the original module sheaf by the original
global multiplication morphisms. Applying the actual derived global
sections functor gives an endomorphism-ring action, independently of any
comparison with Ext. Restriction along the original map to Spec A gives
the A-module structure. The existing canonical Ext comparison is then
linear for these independently specified scalar operations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original multiplication morphisms form the actual coefficient action.
Its laws are proved on the original module-sheaf sections. -/
def coefficientScalarAction {X : Scheme.{u}} (M : X.Modules) :
    Γ(X, ⊤) →+* End M where
  toFun := globalSmulHom M
  map_zero' := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op 0 • x = 0
    rw [map_zero]
    exact (M.val.obj U).isModule.zero_smul x
  map_one' := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op 1 • x = x
    rw [map_one]
    exact (M.val.obj U).isModule.one_smul x
  map_add' r s := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (r + s) • x =
      X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r • x +
        X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s • x
    rw [map_add]
    exact (M.val.obj U).isModule.add_smul _ _ x
  map_mul' r s := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (r * s) • x =
      X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r •
        (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s • x)
    rw [map_mul]
    exact (M.val.obj U).isModule.mul_smul _ _ x

/-- Additivity follows from the original resolution maps, with their original augmentation
commutation equations. No Ext comparison is used. -/
private theorem additive_rightDerived
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).Additive := by
  constructor
  intro X Y f g
  let P := injectiveResolution X
  let Q := injectiveResolution Y
  let f' := InjectiveResolution.desc f Q P
  let g' := InjectiveResolution.desc g Q P
  have wf : P.ι ≫ f' = (CochainComplex.single₀ C).map f ≫ Q.ι :=
    InjectiveResolution.desc_commutes f Q P
  have wg : P.ι ≫ g' = (CochainComplex.single₀ C).map g ≫ Q.ι :=
    InjectiveResolution.desc_commutes g Q P
  have wfg : P.ι ≫ (f' + g') = (CochainComplex.single₀ C).map (f + g) ≫ Q.ι := by
    rw [Preadditive.comp_add, wf, wg, Functor.map_add, Preadditive.add_comp]
  rw [F.rightDerived_map_eq n (f + g) (P := P) (Q := Q) (f' + g') wfg,
    F.rightDerived_map_eq n f (P := P) (Q := Q) f' wf, F.rightDerived_map_eq n g (P := P) (Q := Q) g' wg]
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

/-- The actual functor of derived global sections of the original underlying abelian sheaf. -/
def rightDerivedFunctor (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ AddCommGrp.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    (SheafCochainComparison.globalSectionsFunctor (X : TopCat)).rightDerived n

instance rightDerivedFunctor_additive (X : Scheme.{u}) (n : ℕ) :
    (rightDerivedFunctor X n).Additive := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  let G := (SheafCochainComparison.globalSectionsFunctor (X : TopCat)).rightDerived n
  letI : G.Additive := additive_rightDerived _ n
  change (F ⋙ G).Additive
  constructor
  intro M N f g
  change G.map (F.map (f + g)) = G.map (F.map f) + G.map (F.map g)
  rw [F.map_add, G.map_add]

/-- The original derived target group, with no change of coefficient object. -/
abbrev rightDerivedH {X : Scheme.{u}} (M : X.Modules) (n : ℕ) : Type u :=
  (rightDerivedFunctor X n).obj M

/-- Apply the actual derived functor to the original coefficient ring action.
This construction does not use the Ext comparison or any transported action. -/
def rightDerivedScalarAction {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    Γ(X, ⊤) →+* End ((rightDerivedFunctor X n).obj M) where
  toFun r := (rightDerivedFunctor X n).map (coefficientScalarAction M r)
  map_zero' := by rw [(coefficientScalarAction M).map_zero, Functor.map_zero]
  map_one' := by
    rw [(coefficientScalarAction M).map_one]
    simpa only [End.one_def] using (rightDerivedFunctor X n).map_id M
  map_add' r s := by rw [(coefficientScalarAction M).map_add, Functor.map_add]
  map_mul' r s := by
    rw [(coefficientScalarAction M).map_mul]
    simpa only [End.mul_def] using
      (rightDerivedFunctor X n).map_comp
        (coefficientScalarAction M s) (coefficientScalarAction M r)

/-- The independently defined action of original global functions on the derived target. -/
abbrev rightDerivedGlobalModule {X : Scheme.{u}} (M : X.Modules) (n : ℕ) :
    Module Γ(X, ⊤) (rightDerivedH M n) := by
  change Module Γ(X, ⊤) (ModuleCat.mkOfSMul' (rightDerivedScalarAction M n))
  infer_instance

/-- The actual base ring acts through the original Gamma-Spec map and original f.appTop. -/
abbrev baseRingRightDerivedModule {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (n : ℕ) :
    Module A (rightDerivedH M n) := by
  letI := rightDerivedGlobalModule M n
  exact Module.compHom (rightDerivedH M n)
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)

/-- Its scalar operation is literally the derived map of the original multiplication morphism. -/
theorem baseRingRightDerivedModule_smul
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (n : ℕ)
    (a : A) (x : rightDerivedH M n) :
    letI := baseRingRightDerivedModule f M n
    a • x =
      ((SheafCochainComparison.globalSectionsFunctor (X : TopCat)).rightDerived n).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map
          (globalSmulHom M
            (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) x := rfl

/-- The existing canonical Ext-to-derived comparison is linear for the two original actions. -/
def zariskiRightDerivedLinearEquiv
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (n : ℕ) :
    letI := baseRingModule f M n
    letI := baseRingRightDerivedModule f M n
    H M n ≃ₗ[A] rightDerivedH M n := by
  letI := baseRingModule f M n
  letI := baseRingRightDerivedModule f M n
  refine { ((zariskiRightDerivedIso X n).app M).addCommGroupIsoToAddEquiv with
    map_smul' := ?_ }
  intro a x
  exact zariskiRightDerivedIso_hom_app_smul f M n a x

/-- The linear equivalence retains the original canonical comparison map. -/
theorem zariskiRightDerivedLinearEquiv_apply
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (M : X.Modules) (n : ℕ) (x : H M n) :
    letI := baseRingModule f M n
    letI := baseRingRightDerivedModule f M n
    zariskiRightDerivedLinearEquiv f M n x = (zariskiRightDerivedIso X n).hom.app M x := rfl

end KltDP.Geometry.ModuleCohomology
