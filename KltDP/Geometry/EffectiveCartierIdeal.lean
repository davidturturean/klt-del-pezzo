import KltDP.Geometry.CartierIdealSheafData
import KltDP.Geometry.QuasicoherentIdealKernelIso
import KltDP.Geometry.GluedIdealInvertible

/-!
# The original ideal and zero scheme of an effective Cartier divisor

Regular equations on an integral scheme identify the already defined
ideal O ∩ O(-E) with the original fractional module O(-E). The inverse
map is derived by descent of actual regular sections under O → K.
Both directions retain the original inclusions and local equations.

The same prescribed ideal is the actual image of evaluation on the
original canonical section. Its derived invertibility and quasicoherence
give ideal-sheaf data, the original glued closed immersion, and an actual
isomorphism to its structural kernel. No square-root, separatedness,
Noetherianity, normality or nonempty-divisor hypothesis is used.

Reuse: the existing original Cartier modules and ideal, sheaf-local image
descent, quasicoherent ideal data, and glued-kernel comparison. The source
search and exact endpoint are in docs/reuse_sources/effective_cartier_ideal.
No new ideal, kernel, quotient-gluing or dual-sheaf foundation is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

local instance effectiveCartierIdealCommRing (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

local instance effectiveCartierIdeal_isMulCommutative : ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun _ => ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The inverse of an original Cartier equation represents the negative divisor. -/
theorem CartierEquationChart.neg_represents (E : CartierDivisor X)
    (c : CartierEquationChart X E) :
    cartierEquationClassHom X c.openSet (Additive.ofMul c.equation⁻¹) =
      (cartierDivisorSheaf X).val.map
        (homOfLE (le_top : c.openSet ≤ ⊤)).op (-E) := by
  change cartierEquationClassHom X c.openSet (-(Additive.ofMul c.equation)) = _
  rw [map_neg, c.represents, map_neg]

/-- The natural map from the prescribed intersection ideal to O(-E),
using the original inclusion of regular functions into rational functions. -/
def cartierIdealToNegative (E : CartierDivisor X) :
    (cartierIdealSubmodule X E).toSheafOfModules ⟶ cartierDivisorModule X (-E) where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun s => ⟨(structureToRationalFunctionModule X).val.app U s.val,
            s.property⟩
          map_add' := fun s t => Subtype.ext
            (map_add ((structureToRationalFunctionModule X).val.app U).hom s.val t.val)
          map_smul' := fun a s => Subtype.ext
            (((structureToRationalFunctionModule X).val.app U).hom.map_smul a s.val) }
      naturality := fun {U V} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        apply Subtype.ext
        exact _root_.PresheafOfModules.naturality_apply
          (structureToRationalFunctionModule X).val i s.val }

/-- The natural map preserves both original inclusions into rational functions. -/
@[reassoc]
theorem cartierIdealToNegative_comp_inclusion (E : CartierDivisor X) :
    cartierIdealToNegative X E ≫ cartierDivisorModuleInclusion X (-E) =
      (cartierIdealSubmodule X E).ι ≫ structureToRationalFunctionModule X := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

/-- An original section of O(-E) is an original regular section when the
actual equations of E are regular. The regular section is derived by descent. -/
theorem exists_regularSection_of_negativeCartierSection (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (W : X.Opens)
    (t : (cartierDivisorModule X (-E)).val.obj (op W)) :
    ∃ a : Γ(X, W), (structureToRationalFunctionModule X).val.app (op W) a = t.val := by
  let φ := (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
    (structureToRationalFunctionModule X)
  letI : Mono φ := CategoryTheory.Sheaf.mono_of_injective φ
    (fun U => structureToRationalFunctionModule_app_injective X U.unop)
  apply KltDP.Sheaf.exists_preimage_of_locally_in_image φ W t.val
  intro x hx
  obtain ⟨c, hxc⟩ := hE x
  let V : X.Opens := W ⊓ c.chart.openSet
  letI : Nonempty V := ⟨⟨x, hx, hxc⟩⟩
  let i : V ⟶ W := homOfLE inf_le_left
  let d := RegularCartierEquationChart.restrict X E c V inf_le_right
  let v := (cartierDivisorModule X (-E)).val.map i.op t
  have hv := (mem_cartierSectionSubmodule_iff X (-E) V d.chart.equation⁻¹
    (CartierEquationChart.neg_represents X E d.chart) v.val).mp v.property
  obtain ⟨a, ha⟩ := (mem_principalEquationSubmodule_iff X V d.chart.equation⁻¹ _).mp hv
  -- The restricted coefficient, retyped on the actual open `V`.
  let dc : Γ(X, V) := d.coefficient
  have hg : X.germToFunctionField V dc = (d.chart.equation : X.functionField) := d.germ_eq
  refine ⟨V, i, dc * a, ⟨hx, hxc⟩, ?_⟩
  change (structureToRationalFunctionModule X).val.app (op V) (dc * a) = v.val
  apply (rationalFunctionModuleSectionsEquiv X V).injective
  rw [rationalFunctionModuleSectionsEquiv_structure]
  change X.germToFunctionField V (dc * a) = rationalFunctionModuleSectionsEquiv X V v.val
  rw [map_mul, hg, ha]
  exact Units.mul_inv_cancel_left d.chart.equation _

/-- The original map from the intersection ideal is bijective on every open. -/
theorem cartierIdealToNegative_app_bijective (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (W : X.Opens) :
    Function.Bijective ((cartierIdealToNegative X E).val.app (op W)) := by
  constructor
  · intro s t h
    apply Subtype.ext
    exact structureToRationalFunctionModule_app_injective X W (congrArg Subtype.val h)
  · intro t
    obtain ⟨a, ha⟩ := exists_regularSection_of_negativeCartierSection X E hE W t
    have hm : a ∈ cartierSectionIdeal X E W := by
      change (structureToRationalFunctionModule X).val.app (op W) a ∈
        cartierSectionSubmodule X (-E) W
      rw [ha]
      exact t.property
    exact ⟨⟨a, hm⟩, Subtype.ext ha⟩

private def cartierIdealNegativeIso (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    (cartierIdealSubmodule X E).toSheafOfModules ≅ cartierDivisorModule X (-E) := by
  apply (_root_.SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
  refine _root_.PresheafOfModules.isoMk (fun U =>
    (LinearEquiv.ofBijective ((cartierIdealToNegative X E).val.app U).hom
      (cartierIdealToNegative_app_bijective X E hE U.unop)).toModuleIso) ?_
  intro U V i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact _root_.PresheafOfModules.naturality_apply (cartierIdealToNegative X E).val i s

/-- O(-E) is the actual prescribed ideal subsheaf, with its original normalization. -/
def effectiveCartierNegativeIdealIso (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    cartierDivisorModule X (-E) ≅ (cartierIdealSubmodule X E).toSheafOfModules :=
  (cartierIdealNegativeIso X E hE).symm

/-- The inverse map is the original regular-to-rational map with restricted codomain. -/
@[simp]
theorem effectiveCartierNegativeIdealIso_inv (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    (effectiveCartierNegativeIdealIso X E hE).inv = cartierIdealToNegative X E := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

/-- The inverse isomorphism retains the original rational-function inclusions. -/
@[reassoc]
theorem effectiveCartierNegativeIdealIso_inv_inclusion (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    (effectiveCartierNegativeIdealIso X E hE).inv ≫ cartierDivisorModuleInclusion X (-E) =
      (cartierIdealSubmodule X E).ι ≫ structureToRationalFunctionModule X := by
  rw [effectiveCartierNegativeIdealIso_inv]
  exact cartierIdealToNegative_comp_inclusion X E

/-- The normalized original inclusion O(-E) → O. -/
def effectiveCartierNegativeInclusion (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    cartierDivisorModule X (-E) ⟶ _root_.SheafOfModules.unit X.ringCatSheaf :=
  (effectiveCartierNegativeIdealIso X E hE).hom ≫ (cartierIdealSubmodule X E).ι

/-- Composing the normalized inclusion with O → K gives the original fractional inclusion. -/
@[reassoc]
theorem effectiveCartierNegativeInclusion_comp_rational (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    effectiveCartierNegativeInclusion X E hE ≫ structureToRationalFunctionModule X =
      cartierDivisorModuleInclusion X (-E) := by
  unfold effectiveCartierNegativeInclusion
  rw [Category.assoc, ← effectiveCartierNegativeIdealIso_inv_inclusion,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- On every original open, the included regular section has the original rational value. -/
theorem effectiveCartierNegativeInclusion_app_rational (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (W : X.Opens)
    (t : (cartierDivisorModule X (-E)).val.obj (op W)) :
    (structureToRationalFunctionModule X).val.app (op W)
        ((effectiveCartierNegativeInclusion X E hE).val.app (op W) t) = t.val :=
  congrArg (fun g : cartierDivisorModule X (-E) ⟶ rationalFunctionModule X =>
    g.val.app (op W) t) (effectiveCartierNegativeInclusion_comp_rational X E hE)

/-- The normalized inclusion is multiplication by the original regular equation
in the original frame of O(-E). -/
theorem effectiveCartierNegativeInclusion_equation (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (c : RegularCartierEquationChart X E)
    (a : Γ(X, c.chart.openSet)) :
    (effectiveCartierNegativeInclusion X E hE).val.app (op c.chart.openSet)
        (cartierEquationSectionEquiv X (-E) c.chart.openSet c.chart.equation⁻¹
          (CartierEquationChart.neg_represents X E c.chart) a) = a * c.coefficient := by
  apply structureToRationalFunctionModule_app_injective X c.chart.openSet
  apply (rationalFunctionModuleSectionsEquiv X c.chart.openSet).injective
  rw [effectiveCartierNegativeInclusion_app_rational,
    cartierEquationSectionEquiv_apply_field, rationalFunctionModuleSectionsEquiv_structure]
  change X.germToFunctionField c.chart.openSet a *
      (↑((c.chart.equation⁻¹)⁻¹) : X.functionField) =
    X.germToFunctionField c.chart.openSet (a * c.coefficient)
  rw [inv_inv, map_mul, c.germ_eq]

/-- The actual prescribed ideal is rank one, using the original O(-E) atlas. -/
theorem cartierIdealSubmodule_isInvertible_of_regularEquations (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf)
      (cartierIdealSubmodule X E).toSheafOfModules :=
  KltDP.SheafOfModules.IsInvertible.of_iso (R := X.ringCatSheaf)
    (M := cartierDivisorModule X (-E)) (N := (cartierIdealSubmodule X E).toSheafOfModules)
    (effectiveCartierNegativeIdealIso X E hE)

/-- Quasicoherence is derived for the original ideal subsheaf. -/
theorem cartierIdealSubmodule_isQuasicoherent_of_regularEquations (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    (cartierIdealSubmodule X E).toSheafOfModules.IsQuasicoherent := by
  letI := cartierIdealSubmodule_isInvertible_of_regularEquations X E hE
  infer_instance

private theorem effectiveCartierEvaluation_mem (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (W : X.Opens)
    (φ : (KltDP.SheafOfModules.dual X.ringCatSheaf
      (cartierDivisorModule X E)).val.obj (op W)) :
    (sectionEvaluationMorphism X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE)).val.app (op W) φ ∈ cartierSectionIdeal X E W := by
  apply cartierSectionIdeal_of_locally_mem
  intro x hx
  obtain ⟨c, hxc⟩ := hE x
  let V : X.Opens := W ⊓ c.chart.openSet
  letI : Nonempty V := ⟨⟨x, hx, hxc⟩⟩
  let i : V ⟶ W := homOfLE inf_le_left
  let d := RegularCartierEquationChart.restrict X E c V inf_le_right
  have hlocal : cartierSectionIdeal X E V =
      LinearMap.range ((sectionEvaluationMorphism X (cartierDivisorModule X E)
        (effectiveCartierSection X E hE)).val.app (op V)).hom :=
    (cartierSectionIdeal_eq_span X E d).trans
      (effectiveCartierSection_evaluationMorphism_range X E hE d).symm
  refine ⟨V, i, ⟨hx, hxc⟩, ?_⟩
  rw [hlocal]
  refine ⟨(KltDP.SheafOfModules.dual X.ringCatSheaf
    (cartierDivisorModule X E)).val.map i.op φ, ?_⟩
  exact _root_.PresheafOfModules.naturality_apply
    (sectionEvaluationMorphism X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE)).val i.op φ

/-- Evaluation on the original canonical section factors through the prescribed ideal. -/
def effectiveCartierEvaluationToIdeal (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    KltDP.SheafOfModules.dual X.ringCatSheaf (cartierDivisorModule X E) ⟶
      (cartierIdealSubmodule X E).toSheafOfModules where
  val :=
    { app := fun U => by
        letI : Module (X.ringCatSheaf.val.obj U)
            ((KltDP.SheafOfModules.dualPresheafAb X.ringCatSheaf
              (cartierDivisorModule X E)).obj U) :=
          KltDP.SheafOfModules.dualSectionsModule X.ringCatSheaf
            (cartierDivisorModule X E) U.unop
        exact ModuleCat.ofHom
          { toFun := fun φ => ⟨(sectionEvaluationMorphism X (cartierDivisorModule X E)
                (effectiveCartierSection X E hE)).val.app U φ,
              effectiveCartierEvaluation_mem X E hE U.unop φ⟩
            map_add' := fun φ ψ => Subtype.ext (map_add
              ((sectionEvaluationMorphism X (cartierDivisorModule X E)
                (effectiveCartierSection X E hE)).val.app U).hom φ ψ)
            map_smul' := fun a φ => Subtype.ext
              (((sectionEvaluationMorphism X (cartierDivisorModule X E)
                (effectiveCartierSection X E hE)).val.app U).hom.map_smul a φ) }
      naturality := fun {U V} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply Subtype.ext
        exact _root_.PresheafOfModules.naturality_apply
          (sectionEvaluationMorphism X (cartierDivisorModule X E)
            (effectiveCartierSection X E hE)).val i φ }

/-- This is a factorization of the original evaluation morphism through the original inclusion. -/
@[reassoc]
theorem effectiveCartierEvaluationToIdeal_comp_ι (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    effectiveCartierEvaluationToIdeal X E hE ≫ (cartierIdealSubmodule X E).ι =
      sectionEvaluationMorphism X (cartierDivisorModule X E)
        (effectiveCartierSection X E hE) := by
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rfl

private def effectiveCartierEvaluationFactorisation (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    MonoFactorisation (sectionEvaluationMorphism X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE)) where
  I := (cartierIdealSubmodule X E).toSheafOfModules
  m := (cartierIdealSubmodule X E).ι
  m_mono := inferInstance
  e := effectiveCartierEvaluationToIdeal X E hE
  fac := effectiveCartierEvaluationToIdeal_comp_ι X E hE

/-- The actual categorical image maps into the prescribed ideal by its universal property. -/
def effectiveCartierImageToIdeal (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    sectionImage X (cartierDivisorModule X E) (effectiveCartierSection X E hE) ⟶
      (cartierIdealSubmodule X E).toSheafOfModules :=
  (Abelian.OfCoimageImageComparisonIsIso.imageFactorisation
    (sectionEvaluationMorphism X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE))).isImage.lift
        (effectiveCartierEvaluationFactorisation X E hE)

/-- The image comparison preserves its original inclusion into O. -/
@[reassoc]
theorem effectiveCartierImageToIdeal_comp_ι (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    effectiveCartierImageToIdeal X E hE ≫ (cartierIdealSubmodule X E).ι =
      sectionImageι X (cartierDivisorModule X E) (effectiveCartierSection X E hE) :=
  (Abelian.OfCoimageImageComparisonIsIso.imageFactorisation
    (sectionEvaluationMorphism X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE))).isImage.lift_fac
        (effectiveCartierEvaluationFactorisation X E hE)

/-- The prescribed ideal equals the exact canonical section's image on every open. -/
theorem cartierSectionIdeal_eq_imageIdeal_of_regularEquations (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (W : X.Opens) :
    cartierSectionIdeal X E W = sectionImageIdeal X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE) W := by
  apply le_antisymm
  · intro s hs
    apply sectionImageIdeal_of_locally_mem
    intro x hx
    obtain ⟨c, hxc⟩ := hE x
    let V : X.Opens := W ⊓ c.chart.openSet
    letI : Nonempty V := ⟨⟨x, hx, hxc⟩⟩
    let i : V ⟶ W := homOfLE inf_le_left
    let d := RegularCartierEquationChart.restrict X E c V inf_le_right
    have hm := cartierSectionIdeal_restrict X E i s hs
    have hlocal : cartierSectionIdeal X E V =
        LinearMap.range ((sectionEvaluationMorphism X (cartierDivisorModule X E)
          (effectiveCartierSection X E hE)).val.app (op V)).hom :=
      (cartierSectionIdeal_eq_span X E d).trans
        (effectiveCartierSection_evaluationMorphism_range X E hE d).symm
    refine ⟨V, i, ⟨hx, hxc⟩, ?_⟩
    exact sectionEvaluation_range_le_imageIdeal X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE) V (hlocal.le hm)
  · rintro _ ⟨t, rfl⟩
    have ht := ((effectiveCartierImageToIdeal X E hE).val.app (op W) t).property
    have h := congrArg (fun g : sectionImage X (cartierDivisorModule X E)
        (effectiveCartierSection X E hE) ⟶ _root_.SheafOfModules.unit X.ringCatSheaf =>
      g.val.app (op W) t) (effectiveCartierImageToIdeal_comp_ι X E hE)
    change ((effectiveCartierImageToIdeal X E hE).val.app (op W) t).val =
      (sectionImageι X (cartierDivisorModule X E)
        (effectiveCartierSection X E hE)).val.app (op W) t at h
    exact h ▸ ht

/-- The equality retains the original ideal subsheaves, not only their affine ideals. -/
theorem cartierIdealSubmodule_eq_imageSubmodule_of_regularEquations (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    cartierIdealSubmodule X E = sectionImageSubmodule X (cartierDivisorModule X E)
      (effectiveCartierSection X E hE) := by
  apply _root_.SheafOfModules.Submodule.ext
  apply _root_.PresheafOfModules.Submodule.ext
  intro W
  exact cartierSectionIdeal_eq_imageIdeal_of_regularEquations X E hE W.unop

/-- General ideal-sheaf data from the original effective Cartier ideal. -/
def effectiveCartierIdealDataOfRegularEquations (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) : X.IdealSheafData := by
  letI := cartierIdealSubmodule_isQuasicoherent_of_regularEquations X E hE
  exact QuasicoherentImageIdeal.ofSubmodule (cartierIdealSubmodule X E)

/-- Every affine component is the original prescribed ideal. -/
@[simp]
theorem effectiveCartierIdealDataOfRegularEquations_ideal (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (U : X.affineOpens) :
    (effectiveCartierIdealDataOfRegularEquations X E hE).ideal U =
      cartierSectionIdeal X E U.1 := by
  letI := cartierIdealSubmodule_isQuasicoherent_of_regularEquations X E hE
  exact QuasicoherentImageIdeal.ofSubmodule_ideal (cartierIdealSubmodule X E) U

/-- The constructed scheme ideal has the original canonical-section image. -/
theorem effectiveCartierIdealDataOfRegularEquations_ideal_image (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (U : X.affineOpens) :
    (effectiveCartierIdealDataOfRegularEquations X E hE).ideal U =
      sectionImageIdeal X (cartierDivisorModule X E)
        (effectiveCartierSection X E hE) U.1 := by
  rw [effectiveCartierIdealDataOfRegularEquations_ideal]
  exact cartierSectionIdeal_eq_imageIdeal_of_regularEquations X E hE U.1

/-- Original regular coefficients generate the actual affine ideals. -/
theorem effectiveCartierIdealDataOfRegularEquations_ideal_chart (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (c : RegularCartierEquationChart X E)
    (hc : IsAffineOpen c.chart.openSet) :
    (effectiveCartierIdealDataOfRegularEquations X E hE).ideal ⟨c.chart.openSet, hc⟩ =
      Ideal.span ({c.coefficient} : Set Γ(X, c.chart.openSet)) := by
  rw [effectiveCartierIdealDataOfRegularEquations_ideal]
  exact cartierSectionIdeal_eq_span X E c

/-- The actual glued zero scheme has this original ideal as its structural kernel. -/
@[simp]
theorem effectiveCartierIdealDataOfRegularEquations_ker (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.ker =
      effectiveCartierIdealDataOfRegularEquations X E hE :=
  (effectiveCartierIdealDataOfRegularEquations X E hE).ker_gluedTo

/-- The actual structural map has the original prescribed ideal as its affine section kernel. -/
theorem effectiveCartierIdealDataOfRegularEquations_ker_app (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) (U : X.affineOpens) :
    RingHom.ker ((effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.app U.1).hom =
      cartierSectionIdeal X E U.1 :=
  ((effectiveCartierIdealDataOfRegularEquations X E hE).ker_gluedTo_app U).trans
    (effectiveCartierIdealDataOfRegularEquations_ideal X E hE U)

/-- O(-E) is the actual kernel module of the constructed closed immersion. -/
def effectiveCartierKernelIso (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    cartierDivisorModule X (-E) ≅
      schemeKernelIdeal (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo := by
  letI := cartierIdealSubmodule_isQuasicoherent_of_regularEquations X E hE
  exact effectiveCartierNegativeIdealIso X E hE ≪≫
    QuasicoherentImageIdeal.gluedKernelIso (cartierIdealSubmodule X E)

/-- The actual kernel comparison retains the normalized original inclusion into O. -/
@[reassoc]
theorem effectiveCartierKernelIso_hom_ι (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    (effectiveCartierKernelIso X E hE).hom ≫
        schemeKernelIdealι (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo =
      effectiveCartierNegativeInclusion X E hE := by
  letI := cartierIdealSubmodule_isQuasicoherent_of_regularEquations X E hE
  change ((effectiveCartierNegativeIdealIso X E hE).hom ≫
      (QuasicoherentImageIdeal.gluedKernelIso (cartierIdealSubmodule X E)).hom) ≫
      schemeKernelIdealι (QuasicoherentImageIdeal.ofSubmodule (cartierIdealSubmodule X E)).gluedTo =
    _
  rw [Category.assoc, QuasicoherentImageIdeal.gluedKernelIso_hom_ι]
  rfl

/-- The inverse kernel comparison also preserves the original inclusion. -/
@[reassoc]
theorem effectiveCartierKernelIso_inv_ι (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    (effectiveCartierKernelIso X E hE).inv ≫ effectiveCartierNegativeInclusion X E hE =
      schemeKernelIdealι (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo := by
  rw [← effectiveCartierKernelIso_hom_ι, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The original equations refine to affine nonzerodivisor equations for the zero scheme. -/
theorem effectiveCartierIdealDataOfRegularEquations_regular (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    IdealLocallyPrincipalRegular (effectiveCartierIdealDataOfRegularEquations X E hE) := by
  intro x
  obtain ⟨c, hxc⟩ := hE x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVc⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open hxc c.chart.openSet.2
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let d := RegularCartierEquationChart.restrict X E c V hVc
  refine ⟨⟨V, hV⟩, hxV, d.coefficient,
    effectiveCartierIdealDataOfRegularEquations_ideal_chart X E hE d hV, ?_⟩
  exact mem_nonZeroDivisors_of_ne_zero
    (RegularCartierEquationChart.coefficient_ne_zero X E d)

/-- The actual structural kernel is invertible; the empty closed scheme is allowed. -/
theorem effectiveCartierKernel_isInvertible (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf)
      (schemeKernelIdeal (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo) :=
  KltDP.SheafOfModules.IsInvertible.of_iso (R := X.ringCatSheaf)
    (M := cartierDivisorModule X (-E))
    (N := schemeKernelIdeal (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo)
    (effectiveCartierKernelIso X E hE)

/-- The actual conormal line is supplied by the original affine regular equations. -/
theorem effectiveCartierConormal_isInvertible (E : CartierDivisor X)
    (hE : HasRegularCartierEquations X E) :
    KltDP.SheafOfModules.IsInvertible
      (R := (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued.ringCatSheaf)
      (schemeConormalSheaf (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo) :=
  gluedConormal_isInvertible (effectiveCartierIdealDataOfRegularEquations X E hE)
    (effectiveCartierIdealDataOfRegularEquations_regular X E hE)

section OldSpecialization

local instance effectiveCartierIdeal_monoidalCategory : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- The earlier square-root construction gives the same original ideal data. -/
theorem effectiveCartierIdealData_eq_ofRegularEquations [X.IsSeparated]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E) :
    effectiveCartierIdealData X E hE L e = effectiveCartierIdealDataOfRegularEquations X E hE := by
  apply Scheme.IdealSheafData.ext
  funext U
  exact (effectiveCartierIdealData_ideal X E hE L e U).trans
    (effectiveCartierIdealDataOfRegularEquations_ideal X E hE U).symm

end OldSpecialization

end KltDP.Geometry
