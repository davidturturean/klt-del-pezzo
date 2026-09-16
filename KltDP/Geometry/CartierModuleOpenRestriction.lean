import KltDP.Geometry.CartierOpenRestrictionEquations
import KltDP.Geometry.CartierFractionalOpenRestriction
import KltDP.Geometry.RationalModuleOpenRestriction

/-!
# Actual restriction map on O(D)

Restrict the actual inclusion O(D)→K_X and compose with the actual
rational-module comparison. On an equation chart, the resulting rational
section lies in the transported principal fractional module. The proved
locality criterion then shows that the map lands in O(D restricted).

The construction below is a map of actual module sheaves. Local
bijectivity and the resulting isomorphism are proved separately from the
existing rank-one coordinates; no such isomorphism is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : Y ⟶ X) [IsOpenImmersion f]

/-- The actual restricted O(D) inclusion followed by actual rational
transport. -/
def cartierRestrictionToRational (D : CartierDivisor X) :
    (SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D) ⟶
      rationalFunctionModule Y :=
  (SchemeModuleRestriction.restriction f).map (cartierDivisorModuleInclusion X D) ≫
    (rationalRestrictionIso f).hom

private theorem rationalRestrictionIso_hom_app (V : Y.Opens)
    (s : ((SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X)).val.obj
      (op V)) :
    (rationalRestrictionIso f).hom.val.app (op V) s =
      rationalRestrictionSectionEquiv f V s := rfl

private theorem restrictedCartierInclusion_app (D : CartierDivisor X) (V : Y.Opens)
    (s : ((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.obj
      (op V)) :
    ((SchemeModuleRestriction.restriction f).map
      (cartierDivisorModuleInclusion X D)).val.app (op V) s = s.val := rfl

private theorem cartierRestrictionToRational_app (D : CartierDivisor X) (V : Y.Opens)
    (s : ((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.obj
      (op V)) :
    (cartierRestrictionToRational f D).val.app (op V) s =
      rationalRestrictionSectionEquiv f V s.val := by
  change (rationalRestrictionIso f).hom.val.app (op V)
      (((SchemeModuleRestriction.restriction f).map
        (cartierDivisorModuleInclusion X D)).val.app (op V) s) = _
  rw [restrictedCartierInclusion_app, rationalRestrictionIso_hom_app]

/-- The map is the actual field transport on the original rational
value of the section. -/
theorem cartierRestrictionToRational_field (D : CartierDivisor X)
    (V : Y.Opens) [Nonempty V]
    (s : ((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.obj
      (op V)) :
    letI := nonempty_image f V
    rationalFunctionModuleSectionsEquiv Y V
        ((cartierRestrictionToRational f D).val.app (op V) s) =
      (functionFieldIso f).hom (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) s.val) := by
  letI := nonempty_image f V
  have hfield := rationalRestrictionSectionEquiv_field f V
    (((SchemeModuleRestriction.restriction f).map
      (cartierDivisorModuleInclusion X D)).val.app (op V) s)
  simpa only [cartierRestrictionToRational_app, restrictedCartierInclusion_app] using hfield

/-- On every source equation open, transported rational values lie
in the actual fractional module of the restricted Cartier divisor. -/
theorem cartierRestriction_field_mem_equation (D : CartierDivisor X)
    (W : Y.Opens) [Nonempty W] (g : Y.functionFieldˣ)
    (hg : cartierEquationClassHom Y W (Additive.ofMul g) =
      (cartierDivisorSheaf Y).val.map (homOfLE (show W ≤ ⊤ from le_top)).op
        (cartierRestrictionHom f D))
    (s : ((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.obj
      (op W)) :
    letI := nonempty_image f W
    (functionFieldIso f).hom (rationalFunctionModuleSectionsEquiv X (f ''ᵁ W) s.val) ∈
      principalEquationSubmodule Y W g := by
  letI := nonempty_image f W
  apply mem_principalEquationSubmodule_of_locally_mem Y W g
  intro y hy
  obtain ⟨U, iU, hU, hyU⟩ :=
    cartierEquationCharts_coversTop X D (f ''ᵁ W) (f.base y) ⟨y, hy, rfl⟩
  obtain ⟨c, ⟨iC⟩⟩ := hU
  let V : Y.Opens := f ⁻¹ᵁ U
  letI : Nonempty V := ⟨⟨y, hyU⟩⟩
  letI := nonempty_image f V
  have hVW : V ≤ W := by
    have hpre : V ≤ f ⁻¹ᵁ (f ''ᵁ W) := fun _ hz => iU.le hz
    simpa only [Scheme.Hom.preimage_image_eq] using hpre
  let j : V ⟶ W := homOfLE hVW
  have himage : f ''ᵁ V ≤ c.openSet := by
    have hle : f ''ᵁ (f ⁻¹ᵁ U) ≤ U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inter]
      exact inf_le_right
    exact hle.trans iC.le
  have hc := cartierGlobalEquation_restrict X D
    (U := c.openSet) (V := f ''ᵁ V) (homOfLE himage) c.equation c.represents
  have hcY := cartierRestriction_globalEquation_image f D V c.equation hc
  have hgV := cartierGlobalEquation_restrict Y (cartierRestrictionHom f D)
    (U := W) (V := V) j g hg
  have heq := principalEquationSubmodule_eq_of_class_eq Y V
    (Units.map (functionFieldIso f).hom.hom.toMonoidHom c.equation) g
    (hcY.trans hgV.symm)
  let t : (cartierDivisorModule X D).val.obj (op (f ''ᵁ V)) :=
    ((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.map j.op s
  have hmX := (mem_cartierSectionSubmodule_iff X D (f ''ᵁ V) c.equation hc t.val).mp t.property
  have hmY := (functionFieldIso_mem_principalEquationSubmodule_image_iff f V c.equation
    (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) t.val)).mpr hmX
  have hvalue : rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) t.val =
      rationalFunctionModuleSectionsEquiv X (f ''ᵁ W) s.val :=
    rationalFunctionModuleSectionsEquiv_naturality X (f.opensFunctor.map j) s.val
  refine ⟨V, j, hyU, ?_⟩
  rw [← heq, ← hvalue]
  exact hmY

/-- The actual rational map lands in the defining O(D restricted)
submodule on every open, using its existing locality condition. -/
theorem cartierRestrictionToRational_mem (D : CartierDivisor X) (V : Y.Opens)
    (s : ((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.obj
      (op V)) :
    (cartierRestrictionToRational f D).val.app (op V) s ∈
      cartierSectionSubmodule Y (cartierRestrictionHom f D) V := by
  intro W i hW
  letI := hW
  intro g hg
  have hres := _root_.PresheafOfModules.naturality_apply
    (cartierRestrictionToRational f D).val i.op s
  rw [← hres, cartierRestrictionToRational_field]
  exact cartierRestriction_field_mem_equation f D W g hg _

/-- The actual restriction morphism O_X(D)|Y→O_Y(D|Y), with codomain
restricted by the proved local fractional-module membership. -/
def cartierModuleRestrictionHom (D : CartierDivisor X) :
    (SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D) ⟶
      cartierDivisorModule Y (cartierRestrictionHom f D) := by
  letI (V : Y.Opensᵒᵖ) : Module (Y.ringCatSheaf.val.obj V)
      (((_root_.PresheafOfModules.pushforward₀ f.opensFunctor X.ringCatSheaf.val).obj
        (cartierDivisorModule X D).val).obj V) :=
    (((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.obj V).isModule
  exact _root_.SheafOfModules.Hom.mk {
    app V := ModuleCat.ofHom
      (((cartierRestrictionToRational f D).val.app V).hom.codRestrict
        (cartierSectionSubmodule Y (cartierRestrictionHom f D) V.unop)
        (cartierRestrictionToRational_mem f D V.unop))
    naturality := by
      intro V W i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      apply Subtype.ext
      exact _root_.PresheafOfModules.naturality_apply
        (cartierRestrictionToRational f D).val i s }

private theorem cartierModuleRestrictionHom_app_val (D : CartierDivisor X) (V : Y.Opens)
    (s : ((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.obj
      (op V)) :
    ((cartierModuleRestrictionHom f D).val.app (op V) s).val =
      (cartierRestrictionToRational f D).val.app (op V) s := rfl

/-- The restriction morphism retains the same actual rational value. -/
theorem cartierModuleRestrictionHom_field (D : CartierDivisor X)
    (V : Y.Opens) [Nonempty V]
    (s : ((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.obj
      (op V)) :
    letI := nonempty_image f V
    rationalFunctionModuleSectionsEquiv Y V
        ((cartierModuleRestrictionHom f D).val.app (op V) s).val =
      (functionFieldIso f).hom (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) s.val) := by
  letI := nonempty_image f V
  rw [cartierModuleRestrictionHom_app_val]
  exact cartierRestrictionToRational_field f D V s

end KltDP.Geometry.OpenImmersionRational
