/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see
docs/reuse_sources/section_zero_scheme/upstream/
AINTLIB-160e446617a2168c34c95bbe7a76c4105b392434/LICENSE.
Authors of the upstream dual-precomposition construction: Chris Birkbeck

The small contravariant map on the existing dual sheaf is adapted from
CBirkbeck/AINTLIB 160e446617a2168c34c95bbe7a76c4105b392434,
projects/ModularCurves/ModularCurves/Picard/Dual.lean, lines 654--741.
Changes specialize to the original scheme, use the compatible overFunctor
map and sheaf projections, inline the local linear map, and prove identities
without newer elaborator options. The dual object itself is imported.
-/
import KltDP.Geometry.SectionEffectiveCartier
import KltDP.Geometry.EffectiveCartierIdeal

/-!
# The actual zero scheme of an original nonzero invertible-sheaf section

Precomposition on the original local functionals preserves evaluation and
therefore transports the actual section-image ideal through an original
section-preserving isomorphism. On an integral scheme, regular Cartier
equations make canonical-section evaluation monic. Its actual image factor
identifies the original dual with O(-E), retaining the normalized inclusion.

The original section-image subsheaf is consequently invertible and
quasicoherent. Existing ideal data and quotient gluing construct its actual
closed zero scheme. The original dual is its actual structural kernel, with
evaluation as its inclusion. No square root, separatedness, Riemann--Roch,
vanishing, nonempty zero scheme or chosen inverse line is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace

universe u

namespace KltDP.Geometry

open KltDP.SheafOfModules

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u})

local instance sectionZeroCommRing (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

local instance sectionZeroScheme_isMulCommutative : ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun _ => ⟨⟨fun a b => mul_comm a b⟩⟩

/-- Precompose actual local functionals by the original module morphism. -/
def sectionDualMap {M N : X.Modules} (f : M ⟶ N) :
    dual X.ringCatSheaf N ⟶ dual X.ringCatSheaf M where
  val :=
    { app := fun U => by
        letI := dualSectionsModule X.ringCatSheaf N U.unop
        letI := dualSectionsModule X.ringCatSheaf M U.unop
        change ModuleCat.of (X.ringCatSheaf.val.obj U)
            (N.over U.unop ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U.unop)) ⟶
          ModuleCat.of (X.ringCatSheaf.val.obj U)
            (M.over U.unop ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U.unop))
        exact ModuleCat.ofHom
          { toFun := fun φ => (_root_.SheafOfModules.overFunctor X.ringCatSheaf U.unop).map f ≫ φ
            map_add' := fun φ ψ => Preadditive.comp_add _ _ _ _ φ ψ
            map_smul' := fun r φ => by
              change (_root_.SheafOfModules.overFunctor X.ringCatSheaf U.unop).map f ≫
                  (φ ≫ overUnitScalarEnd X.ringCatSheaf U.unop r) =
                ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U.unop).map f ≫ φ) ≫
                  overUnitScalarEnd X.ringCatSheaf U.unop r
              exact (Category.assoc _ _ _).symm }
      naturality := fun {U V} g => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        rfl }

/-- The original over-site precomposition is the actual component map. -/
@[simp]
theorem sectionDualMap_app {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (φ : (dual X.ringCatSheaf N).val.obj (op U)) :
    (sectionDualMap X f).val.app (op U) φ =
      (_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map f ≫ φ := rfl

@[simp]
theorem sectionDualMap_id (M : X.Modules) :
    sectionDualMap X (𝟙 M) = 𝟙 (dual X.ringCatSheaf M) := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (_root_.SheafOfModules.overFunctor X.ringCatSheaf U.unop).map (𝟙 M) ≫ φ = φ
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

@[simp]
theorem sectionDualMap_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    sectionDualMap X (f ≫ g) = sectionDualMap X g ≫ sectionDualMap X f := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (_root_.SheafOfModules.overFunctor X.ringCatSheaf U.unop).map (f ≫ g) ≫ φ =
    (_root_.SheafOfModules.overFunctor X.ringCatSheaf U.unop).map f ≫
      ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U.unop).map g ≫ φ)
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- An actual isomorphism induces the reverse isomorphism of the original duals. -/
def sectionDualIso {M N : X.Modules} (e : M ≅ N) :
    dual X.ringCatSheaf N ≅ dual X.ringCatSheaf M where
  hom := sectionDualMap X e.hom
  inv := sectionDualMap X e.inv
  hom_inv_id := by rw [← sectionDualMap_comp, e.inv_hom_id, sectionDualMap_id]
  inv_hom_id := by rw [← sectionDualMap_comp, e.hom_inv_id, sectionDualMap_id]

/-- Evaluation commutes with precomposition using the original identity restriction. -/
theorem evalSection_precomp {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (φ : N.over U ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : M.val.obj (op U)) :
    evalSection X.ringCatSheaf M U
        ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map f ≫ φ) m =
      evalSection X.ringCatSheaf N U φ (f.val.app (op U) m) := by
  change φ.val.app (op (Over.mk (𝟙 U)))
      (f.val.app (op U) (M.val.map (𝟙 U).op m)) =
    φ.val.app (op (Over.mk (𝟙 U))) (N.val.map (𝟙 U).op (f.val.app (op U) m))
  exact congrArg (fun n => φ.val.app (op (Over.mk (𝟙 U))) n)
    (_root_.PresheafOfModules.naturality_apply f.val (𝟙 U).op m)

/-- The equality is between the original global evaluation morphisms. -/
@[reassoc]
theorem sectionDualMap_comp_evaluation {M N : X.Modules} (f : M ⟶ N)
    (s : M.val.obj (op (⊤ : X.Opens))) :
    sectionDualMap X f ≫ sectionEvaluationMorphism X M s =
      sectionEvaluationMorphism X N (f.val.app (op (⊤ : X.Opens)) s) := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change evalSection X.ringCatSheaf M U.unop
      ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U.unop).map f ≫ φ)
      (M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s) =
    evalSection X.ringCatSheaf N U.unop φ
      (N.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f.val.app (op (⊤ : X.Opens)) s))
  rw [evalSection_precomp]
  exact congrArg (evalSection X.ringCatSheaf N U.unop φ)
    (_root_.PresheafOfModules.naturality_apply f.val
      (homOfLE (le_top : U.unop ≤ ⊤)).op s)

private theorem sectionImageIdeal_le_of_evaluation_factor (M N : X.Modules)
    (s : M.val.obj (op (⊤ : X.Opens))) (t : N.val.obj (op (⊤ : X.Opens)))
    (a : dual X.ringCatSheaf N ⟶ dual X.ringCatSheaf M)
    (h : a ≫ sectionEvaluationMorphism X M s = sectionEvaluationMorphism X N t)
    (W : X.Opens) : sectionImageIdeal X N t W ≤ sectionImageIdeal X M s W := by
  let F : MonoFactorisation (sectionEvaluationMorphism X N t) :=
    { I := sectionImage X M s
      m := sectionImageι X M s
      m_mono := inferInstance
      e := a ≫ Abelian.factorThruImage (sectionEvaluationMorphism X M s)
      fac := by rw [Category.assoc, sectionImage_factorization, h] }
  let p : sectionImage X N t ⟶ sectionImage X M s :=
    (Abelian.OfCoimageImageComparisonIsIso.imageFactorisation
      (sectionEvaluationMorphism X N t)).isImage.lift F
  have hp : p ≫ sectionImageι X M s = sectionImageι X N t :=
    (Abelian.OfCoimageImageComparisonIsIso.imageFactorisation
      (sectionEvaluationMorphism X N t)).isImage.lift_fac F
  rintro _ ⟨z, rfl⟩
  refine ⟨p.val.app (op W) z, ?_⟩
  exact congrArg (fun f : sectionImage X N t ⟶ _root_.SheafOfModules.unit X.ringCatSheaf =>
    f.val.app (op W) z) hp

/-- A section-preserving isomorphism preserves the original image ideals on every open. -/
theorem sectionImageIdeal_eq_of_iso {M N : X.Modules} (e : M ≅ N)
    (s : M.val.obj (op (⊤ : X.Opens))) (t : N.val.obj (op (⊤ : X.Opens)))
    (he : e.hom.val.app (op (⊤ : X.Opens)) s = t) (W : X.Opens) :
    sectionImageIdeal X M s W = sectionImageIdeal X N t W := by
  have hback : e.inv.val.app (op (⊤ : X.Opens)) t = s := by
    rw [← he]
    exact congrArg (fun f : M ⟶ M => f.val.app (op (⊤ : X.Opens)) s) e.hom_inv_id
  apply le_antisymm
  · exact sectionImageIdeal_le_of_evaluation_factor X N M t s (sectionDualMap X e.inv)
      ((sectionDualMap_comp_evaluation X e.inv t).trans
        (congrArg (sectionEvaluationMorphism X M) hback)) W
  · exact sectionImageIdeal_le_of_evaluation_factor X M N s t (sectionDualMap X e.hom)
      ((sectionDualMap_comp_evaluation X e.hom s).trans
        (congrArg (sectionEvaluationMorphism X N) he)) W

/-- The equality retains the actual ideal subsheaves of the original structure sheaf. -/
theorem sectionImageSubmodule_eq_of_iso {M N : X.Modules} (e : M ≅ N)
    (s : M.val.obj (op (⊤ : X.Opens))) (t : N.val.obj (op (⊤ : X.Opens)))
    (he : e.hom.val.app (op (⊤ : X.Opens)) s = t) :
    sectionImageSubmodule X M s = sectionImageSubmodule X N t := by
  apply _root_.SheafOfModules.Submodule.ext
  apply _root_.PresheafOfModules.Submodule.ext
  intro W
  exact sectionImageIdeal_eq_of_iso X e s t he W.unop

variable [IsIntegral X]

/-- Nonzero original regular equations make canonical-section evaluation injective. -/
theorem effectiveCartierEvaluation_chart_injective (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (c : RegularCartierEquationChart X E) :
    Function.Injective ((sectionEvaluationMorphism X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE)).val.app (op c.chart.openSet)) := by
  letI : Nonempty c.chart.openSet := c.chart.nonempty
  let τ := (cartierEquationOverIso X E c.chart.openSet
    c.chart.equation c.chart.represents).symm
  have hf (φ : (dual X.ringCatSheaf (cartierDivisorModule X E)).val.obj
      (op c.chart.openSet)) :
      (sectionEvaluationMorphism X (cartierDivisorModule X E)
        (effectiveCartierSection X E hE)).val.app (op c.chart.openSet) φ =
      (show Γ(X, c.chart.openSet) from
        dualUnitSectionsEquiv X.ringCatSheaf c.chart.openSet (τ.inv ≫ φ)) * c.coefficient := by
    change evalSection X.ringCatSheaf (cartierDivisorModule X E) c.chart.openSet φ _ = _
    rw [evalSection_factor X.ringCatSheaf (cartierDivisorModule X E) c.chart.openSet τ]
    exact congrArg (fun r => dualUnitSectionsEquiv X.ringCatSheaf c.chart.openSet
      (τ.inv ≫ φ) * r) (effectiveCartierSection_frame_eval X E hE c)
  intro φ ψ h
  apply (cancel_epi τ.inv).mp
  apply (dualUnitSectionsEquiv X.ringCatSheaf c.chart.openSet).injective
  apply mul_right_cancel₀ (M₀ := Γ(X, c.chart.openSet))
    (RegularCartierEquationChart.coefficient_ne_zero X E c)
  exact (hf φ).symm.trans (h.trans (hf ψ))

/-- Injectivity of evaluation on an open follows from injectivity on an actual open
cover of it, by the dual sheaf condition. The module is kept abstract here so that the
sheaf-condition unification never unfolds a concrete divisor module. -/
private theorem sectionEvaluation_open_injective_of_locally (N : X.Modules)
    (b : N.val.obj (op (⊤ : X.Opens))) (W : X.Opens)
    (hloc : ∀ x ∈ W, ∃ V : X.Opens, V ≤ W ∧ x ∈ V ∧
      Function.Injective ((sectionEvaluationMorphism X N b).val.app (op V))) :
    Function.Injective ((sectionEvaluationMorphism X N b).val.app (op W)) := by
  intro φ ψ h
  apply TopCat.Presheaf.IsSheaf.section_ext
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj (dual X.ringCatSheaf N)).cond
  intro x hx
  obtain ⟨V, hVW, hxV, hinj⟩ := hloc x hx
  refine ⟨V, hVW, hxV, ?_⟩
  change (dual X.ringCatSheaf N).val.map (homOfLE hVW).op φ =
    (dual X.ringCatSheaf N).val.map (homOfLE hVW).op ψ
  apply hinj
  rw [_root_.PresheafOfModules.naturality_apply,
    _root_.PresheafOfModules.naturality_apply, h]

/-- Actual sheaf locality proves injectivity on all opens, including the empty open. -/
theorem effectiveCartierEvaluation_open_injective (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (W : X.Opens) :
    Function.Injective ((sectionEvaluationMorphism X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE)).val.app (op W)) := by
  apply sectionEvaluation_open_injective_of_locally
  intro x hx
  obtain ⟨c, hxc⟩ := hE x
  let V : X.Opens := W ⊓ c.chart.openSet
  letI : Nonempty V := ⟨⟨x, hx, hxc⟩⟩
  exact ⟨V, inf_le_left, ⟨hx, hxc⟩,
    effectiveCartierEvaluation_chart_injective X E hE
      (RegularCartierEquationChart.restrict X E c V inf_le_right)⟩

/-- Canonical-section evaluation is monic without a square-root premise. -/
theorem effectiveCartierEvaluation_mono (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    Mono (sectionEvaluationMorphism X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE)) := by
  have h : Mono ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
      (sectionEvaluationMorphism X (cartierDivisorModule X E)
        (effectiveCartierSection X E hE))) :=
    CategoryTheory.Sheaf.mono_of_injective _
      (fun W => effectiveCartierEvaluation_open_injective X E hE W.unop)
  exact (_root_.SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map h

private theorem idealSubmodule_eqToIso_hom_ι
    (I J : (_root_.SheafOfModules.unit X.ringCatSheaf).Submodule) (h : I = J) :
    (eqToIso (congrArg (fun P => P.toSheafOfModules) h)).hom ≫ J.ι = I.ι := by
  cases h
  exact Category.id_comp _

/-- Transport of an original ideal subsheaf along an equality of submodules. -/
private def idealSubmoduleEqIso
    (I J : (_root_.SheafOfModules.unit X.ringCatSheaf).Submodule) (h : I = J) :
    I.toSheafOfModules ≅ J.toSheafOfModules :=
  eqToIso (congrArg (fun P => P.toSheafOfModules) h)

private theorem idealSubmoduleEqIso_hom_ι
    (I J : (_root_.SheafOfModules.unit X.ringCatSheaf).Submodule) (h : I = J) :
    (idealSubmoduleEqIso X I J h).hom ≫ J.ι = I.ι :=
  idealSubmodule_eqToIso_hom_ι X I J h

/-- The actual canonical evaluation image identifies the original dual with the original ideal. -/
def effectiveCartierDualIdealIso (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    dual X.ringCatSheaf (cartierDivisorModule X E) ≅
      (cartierIdealSubmodule X E).toSheafOfModules := by
  letI := effectiveCartierEvaluation_mono X E hE
  exact asIso (Abelian.factorThruImage (sectionEvaluationMorphism X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE))) ≪≫
    sectionImageIsoSubmodule X (cartierDivisorModule X E) (effectiveCartierSection X E hE) ≪≫
    idealSubmoduleEqIso X _ _
      (cartierIdealSubmodule_eq_imageSubmodule_of_regularEquations X E hE).symm

/-- This dual comparison retains the original canonical-section evaluation as its inclusion. -/
@[reassoc]
theorem effectiveCartierDualIdealIso_hom_ι (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    (effectiveCartierDualIdealIso X E hE).hom ≫ (cartierIdealSubmodule X E).ι =
      sectionEvaluationMorphism X (cartierDivisorModule X E)
        (effectiveCartierSection X E hE) := by
  simp only [effectiveCartierDualIdealIso, Iso.trans_hom, asIso_hom, Category.assoc,
    idealSubmoduleEqIso_hom_ι, sectionImageIsoSubmodule_hom_ι, sectionImage_factorization]

/-- The section-preserving Cartier isomorphism identifies the original dual with O(-E). -/
def sectionPreservingCartierDualIso (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (M : X.Modules)
    (e : cartierDivisorModule X E ≅ M) :
    dual X.ringCatSheaf M ≅ cartierDivisorModule X (-E) :=
  sectionDualIso X e ≪≫ effectiveCartierDualIdealIso X E hE ≪≫
    (effectiveCartierNegativeIdealIso X E hE).symm

/-- The inverse line has the original evaluation normalization, fixed by the original section. -/
@[reassoc]
theorem sectionPreservingCartierDualIso_hom_ι (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (M : X.Modules)
    (e : cartierDivisorModule X E ≅ M) (s : M.val.obj (op (⊤ : X.Opens)))
    (he : e.hom.val.app (op (⊤ : X.Opens)) (effectiveCartierSection X E hE) = s) :
    (sectionPreservingCartierDualIso X E hE M e).hom ≫
        effectiveCartierNegativeInclusion X E hE = sectionEvaluationMorphism X M s := by
  simp only [sectionPreservingCartierDualIso, Iso.trans_hom, Iso.symm_hom,
    effectiveCartierNegativeInclusion, Category.assoc, Iso.inv_hom_id_assoc,
    effectiveCartierDualIdealIso_hom_ι]
  exact (sectionDualMap_comp_evaluation X e.hom (effectiveCartierSection X E hE)).trans
    (congrArg (sectionEvaluationMorphism X M) he)

/-- The reverse comparison also preserves the original normalized inclusion. -/
@[reassoc]
theorem sectionPreservingCartierDualIso_inv_ι (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (M : X.Modules)
    (e : cartierDivisorModule X E ≅ M) (s : M.val.obj (op (⊤ : X.Opens)))
    (he : e.hom.val.app (op (⊤ : X.Opens)) (effectiveCartierSection X E hE) = s) :
    (sectionPreservingCartierDualIso X E hE M e).inv ≫ sectionEvaluationMorphism X M s =
      effectiveCartierNegativeInclusion X E hE := by
  rw [← sectionPreservingCartierDualIso_hom_ι X E hE M e s he,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Evaluation on the original nonzero invertible-sheaf section is monic. -/
theorem nonzeroSectionEvaluation_mono (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    Mono (sectionEvaluationMorphism X L.obj s) := by
  obtain ⟨E, hE, e, he⟩ := exists_effectiveCartier_of_nonzero_section X L s hs
  letI := effectiveCartierEvaluation_mono X E hE
  have h := (sectionDualMap_comp_evaluation X e.hom (effectiveCartierSection X E hE)).trans
    (congrArg (sectionEvaluationMorphism X L.obj) he)
  rw [← h]
  change Mono ((sectionDualIso X e).hom ≫ sectionEvaluationMorphism X (cartierDivisorModule X E)
    (effectiveCartierSection X E hE))
  infer_instance

/-- The original section-image subsheaf is invertible, with no chosen ideal substituted. -/
theorem nonzeroSectionImage_isInvertible (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf)
      (sectionImageSubmodule X L.obj s).toSheafOfModules := by
  obtain ⟨E, hE, e, he⟩ := exists_effectiveCartier_of_nonzero_section X L s hs
  rw [← sectionImageSubmodule_eq_of_iso X e (effectiveCartierSection X E hE) s he,
    ← cartierIdealSubmodule_eq_imageSubmodule_of_regularEquations X E hE]
  exact cartierIdealSubmodule_isInvertible_of_regularEquations X E hE

/-- Quasicoherence is derived for that same original section-image subsheaf. -/
theorem nonzeroSectionImage_isQuasicoherent (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    (sectionImageSubmodule X L.obj s).toSheafOfModules.IsQuasicoherent := by
  letI := nonzeroSectionImage_isInvertible X L s hs
  infer_instance

/-- Existing ideal data applied to the original section-image subsheaf with proved quasicoherence. -/
def nonzeroSectionIdealData (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) : X.IdealSheafData := by
  letI := nonzeroSectionImage_isQuasicoherent X L s hs
  exact QuasicoherentImageIdeal.ofSubmodule (sectionImageSubmodule X L.obj s)

/-- Every affine ideal is the original section-image ideal. -/
@[simp]
theorem nonzeroSectionIdealData_ideal (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) (U : X.affineOpens) :
    (nonzeroSectionIdealData X L s hs).ideal U = sectionImageIdeal X L.obj s U.1 := by
  letI := nonzeroSectionImage_isQuasicoherent X L s hs
  exact QuasicoherentImageIdeal.ofSubmodule_ideal (sectionImageSubmodule X L.obj s) U

/-- The existing quotient gluing is an actual closed immersion for the original zero ideal. -/
theorem nonzeroSectionZero_isClosedImmersion (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    IsClosedImmersion (nonzeroSectionIdealData X L s hs).gluedTo := inferInstance

/-- Its actual structural kernel is exactly the original section-image ideal data. -/
@[simp]
theorem nonzeroSectionIdealData_ker (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    (nonzeroSectionIdealData X L s hs).gluedTo.ker = nonzeroSectionIdealData X L s hs :=
  (nonzeroSectionIdealData X L s hs).ker_gluedTo

/-- The actual affine section kernels retain the original evaluation image. -/
theorem nonzeroSectionIdealData_ker_app (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) (U : X.affineOpens) :
    RingHom.ker ((nonzeroSectionIdealData X L s hs).gluedTo.app U.1).hom =
      sectionImageIdeal X L.obj s U.1 :=
  ((nonzeroSectionIdealData X L s hs).ker_gluedTo_app U).trans
    (nonzeroSectionIdealData_ideal X L s hs U)

/-- The original dual, via its original image factor, is the actual zero-scheme kernel. -/
def nonzeroSectionDualKernelIso (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    dual X.ringCatSheaf L.obj ≅ schemeKernelIdeal (nonzeroSectionIdealData X L s hs).gluedTo := by
  letI := nonzeroSectionEvaluation_mono X L s hs
  letI := nonzeroSectionImage_isQuasicoherent X L s hs
  exact asIso (Abelian.factorThruImage (sectionEvaluationMorphism X L.obj s)) ≪≫
    sectionImageIsoSubmodule X L.obj s ≪≫
    QuasicoherentImageIdeal.gluedKernelIso (sectionImageSubmodule X L.obj s)

/-- The kernel inclusion is the original dual-evaluation morphism, with no unspecified unit. -/
@[reassoc]
theorem nonzeroSectionDualKernelIso_hom_ι (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    (nonzeroSectionDualKernelIso X L s hs).hom ≫
        schemeKernelIdealι (nonzeroSectionIdealData X L s hs).gluedTo =
      sectionEvaluationMorphism X L.obj s := by
  letI := nonzeroSectionImage_isQuasicoherent X L s hs
  change ((Abelian.factorThruImage (sectionEvaluationMorphism X L.obj s) ≫
    (sectionImageIsoSubmodule X L.obj s).hom) ≫
    (QuasicoherentImageIdeal.gluedKernelIso (sectionImageSubmodule X L.obj s)).hom) ≫
    schemeKernelIdealι
      (QuasicoherentImageIdeal.ofSubmodule (sectionImageSubmodule X L.obj s)).gluedTo = _
  rw [Category.assoc, QuasicoherentImageIdeal.gluedKernelIso_hom_ι,
    Category.assoc, sectionImageIsoSubmodule_hom_ι, sectionImage_factorization]

/-- The inverse kernel comparison retains the same original evaluation. -/
@[reassoc]
theorem nonzeroSectionDualKernelIso_inv_ι (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    (nonzeroSectionDualKernelIso X L s hs).inv ≫ sectionEvaluationMorphism X L.obj s =
      schemeKernelIdealι (nonzeroSectionIdealData X L s hs).gluedTo := by
  rw [← nonzeroSectionDualKernelIso_hom_ι X L s hs,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The constructed Cartier representative preserves the original section, all-open ideals,
actual zero-scheme ideal data, and the original dual with its normalized inclusion. -/
theorem exists_effectiveCartier_zeroScheme_of_nonzero_section (L : InvertibleSheaf X)
    (s : L.obj.val.obj (op (⊤ : X.Opens))) (hs : s ≠ 0) :
    ∃ (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
      (e : cartierDivisorModule X E ≅ L.obj),
      e.hom.val.app (op (⊤ : X.Opens)) (effectiveCartierSection X E hE) = s ∧
      (∀ W : X.Opens, sectionImageIdeal X L.obj s W = cartierSectionIdeal X E W) ∧
      nonzeroSectionIdealData X L s hs = effectiveCartierIdealDataOfRegularEquations X E hE ∧
      ∃ η : dual X.ringCatSheaf L.obj ≅ cartierDivisorModule X (-E),
        η.hom ≫ effectiveCartierNegativeInclusion X E hE = sectionEvaluationMorphism X L.obj s ∧
        η.inv ≫ sectionEvaluationMorphism X L.obj s = effectiveCartierNegativeInclusion X E hE := by
  obtain ⟨E, hE, e, he⟩ := exists_effectiveCartier_of_nonzero_section X L s hs
  have hI (W : X.Opens) : sectionImageIdeal X L.obj s W = cartierSectionIdeal X E W :=
    (sectionImageIdeal_eq_of_iso X e (effectiveCartierSection X E hE) s he W).symm.trans
      (cartierSectionIdeal_eq_imageIdeal_of_regularEquations X E hE W).symm
  refine ⟨E, hE, e, he, hI, ?_, sectionPreservingCartierDualIso X E hE L.obj e,
    sectionPreservingCartierDualIso_hom_ι X E hE L.obj e s he,
    sectionPreservingCartierDualIso_inv_ι X E hE L.obj e s he⟩
  apply Scheme.IdealSheafData.ext
  funext U
  exact (nonzeroSectionIdealData_ideal X L s hs U).trans
    ((hI U.1).trans (effectiveCartierIdealDataOfRegularEquations_ideal X E hE U).symm)

end KltDP.Geometry
