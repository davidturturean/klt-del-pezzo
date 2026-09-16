import KltDP.Geometry.CartierDivisorTrivialization
import KltDP.Geometry.QuadraticSectionImageIntegral

/-!
# The canonical section of an original Cartier divisor with regular equations

The Cartier divisor is the existing global section of the actual quotient
sheaf. Regular equation charts add only original regular functions whose
function-field images represent that divisor. If these charts cover X,
locality of the already constructed O(D) subsheaf puts the actual rational
function 1 in O(D). Its canonical section is nonzero, and its coefficient
in an original equation frame is the original regular equation.

The actual dual-evaluation image therefore has the prescribed principal
ideal on each such chart. This supplies a section for an original divisor,
rather than naming an arbitrary quotient the branch divisor. It does not
derive regular equations for a geometric sum of nodes, identify a global
closed subscheme with that sum, or prove its reducedness or smoothness.
Those original geometric inputs remain separate. No characteristic or
normality assumption is required for this integral-scheme construction.

Reuse: original Cartier fractional modules and their locality/frame maps,
original structure-to-rational-functions map, and the existing actual
dual-evaluation image comparison. Pinned and newer official Mathlib's
ideal-subscheme APIs do not supply this original Cartier-section adapter.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- An original Cartier equation chart together with an actual regular
section representing its rational equation. No zero ideal is supplied. -/
structure RegularCartierEquationChart (D : CartierDivisor X) where
  chart : CartierEquationChart X D
  coefficient : Γ(X, chart.openSet)
  germ_eq : X.germToFunctionField chart.openSet coefficient =
    (chart.equation : X.functionField)

/-- Literal regular equation charts cover the original scheme. -/
def HasRegularCartierEquations (D : CartierDivisor X) : Prop :=
  ∀ x : X, ∃ c : RegularCartierEquationChart X D, x ∈ c.chart.openSet

private theorem rationalOne_restrict {U V : X.Opens} (i : V ⟶ U) :
    (rationalFunctionModule X).val.map i.op
        ((structureToRationalFunctionModule X).val.app (op U) (1 : Γ(X, U))) =
      (structureToRationalFunctionModule X).val.app (op V) (1 : Γ(X, V)) := by
  calc
    _ = (structureToRationalFunctionModule X).val.app (op V)
        ((_root_.SheafOfModules.unit X.ringCatSheaf).val.map i.op (1 : Γ(X, U))) :=
      (_root_.PresheafOfModules.naturality_apply
        (structureToRationalFunctionModule X).val i.op (1 : Γ(X, U))).symm
    _ = _ := congrArg ((structureToRationalFunctionModule X).val.app (op V))
      ((X.presheaf.map i.op).hom.map_one)

/-- Every actual regular equation is nonzero in its original section ring. -/
theorem RegularCartierEquationChart.coefficient_ne_zero (D : CartierDivisor X)
    (c : RegularCartierEquationChart X D) : c.coefficient ≠ 0 := by
  intro h
  have hz := c.germ_eq
  rw [h, map_zero] at hz
  exact (Units.ne_zero c.chart.equation) hz.symm

/-- The original local equations, together with proved sheaf locality,
put rational one in the actual global fractional module O(D). -/
theorem rationalOne_mem_cartierSectionSubmodule (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) :
    (structureToRationalFunctionModule X).val.app (op (⊤ : X.Opens)) (1 : Γ(X, ⊤)) ∈
      cartierSectionSubmodule X D ⊤ := by
  apply cartierDivisorPresheafSubmodule_isSheaf X D
  intro x hx
  obtain ⟨c, hxc⟩ := hD x
  refine ⟨c.chart.openSet, homOfLE (show c.chart.openSet ≤ ⊤ from le_top), ?_, hxc⟩
  change (rationalFunctionModule X).val.map _
      ((structureToRationalFunctionModule X).val.app (op (⊤ : X.Opens)) (1 : Γ(X, ⊤))) ∈
    cartierSectionSubmodule X D c.chart.openSet
  rw [rationalOne_restrict]
  apply (mem_cartierSectionSubmodule_iff X D c.chart.openSet c.chart.equation
    c.chart.represents _).mpr
  rw [rationalFunctionModuleSectionsEquiv_structure, map_one]
  exact (mem_principalEquationSubmodule_iff X c.chart.openSet c.chart.equation 1).mpr
    ⟨c.coefficient, by simpa only [mul_one] using c.germ_eq⟩

/-- The canonical section of the original Cartier divisor is literally
the image of regular one in the actual rational-function subsheaf. -/
def effectiveCartierSection (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) :
    (cartierDivisorModule X D).val.obj (op (⊤ : X.Opens)) :=
  ⟨(structureToRationalFunctionModule X).val.app (op (⊤ : X.Opens)) (1 : Γ(X, ⊤)),
    rationalOne_mem_cartierSectionSubmodule X D hD⟩

/-- The constructed section is nonzero in the original module. -/
theorem effectiveCartierSection_ne_zero (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) : effectiveCartierSection X D hD ≠ 0 := by
  intro h
  have hval := congrArg
    (fun s : (cartierDivisorModule X D).val.obj (op (⊤ : X.Opens)) => s.val) h
  have hk := congrArg (rationalFunctionModuleSectionsEquiv X (⊤ : X.Opens)) hval
  change rationalFunctionModuleSectionsEquiv X ⊤
      ((structureToRationalFunctionModule X).val.app (op (⊤ : X.Opens)) (1 : Γ(X, ⊤))) =
    rationalFunctionModuleSectionsEquiv X ⊤ 0 at hk
  rw [rationalFunctionModuleSectionsEquiv_structure, map_one, map_zero] at hk
  exact one_ne_zero hk

/-- The original Cartier frame sends the original equation to the
restriction of the canonical section, with the convention O(D)=f⁻¹O. -/
theorem effectiveCartierSection_eq_equation_frame (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (c : RegularCartierEquationChart X D) :
    (cartierDivisorModule X D).val.map
        (homOfLE (le_top : c.chart.openSet ≤ ⊤)).op (effectiveCartierSection X D hD) =
      cartierEquationSectionEquiv X D c.chart.openSet c.chart.equation
        c.chart.represents c.coefficient := by
  apply Subtype.ext
  apply (rationalFunctionModuleSectionsEquiv X c.chart.openSet).injective
  change rationalFunctionModuleSectionsEquiv X c.chart.openSet
      ((rationalFunctionModule X).val.map
        (homOfLE (le_top : c.chart.openSet ≤ ⊤)).op
        ((structureToRationalFunctionModule X).val.app (op (⊤ : X.Opens)) (1 : Γ(X, ⊤)))) = _
  rw [rationalOne_restrict, rationalFunctionModuleSectionsEquiv_structure, map_one,
    cartierEquationSectionEquiv_apply_field, c.germ_eq]
  exact (Units.mul_inv c.chart.equation).symm

/-- Inverse coordinates of the actual restricted section are precisely
the regular equation of the prescribed original Cartier divisor. -/
theorem effectiveCartierSection_coordinate (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (c : RegularCartierEquationChart X D) :
    (cartierEquationSectionEquiv X D c.chart.openSet c.chart.equation
      c.chart.represents).symm
      ((cartierDivisorModule X D).val.map
        (homOfLE (le_top : c.chart.openSet ≤ ⊤)).op (effectiveCartierSection X D hD)) =
      c.coefficient := by
  rw [effectiveCartierSection_eq_equation_frame, LinearEquiv.symm_apply_apply]

/-- The genuine module-dual evaluation ideal of this original section
is its original Cartier equation ideal, before any quotient is formed. -/
theorem effectiveCartierSection_evaluationIdeal (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (c : RegularCartierEquationChart X D) :
    sectionEvaluationIdeal X (cartierDivisorModule X D) (effectiveCartierSection X D hD)
      c.chart.openSet = Ideal.span ({c.coefficient} : Set Γ(X, c.chart.openSet)) := by
  change LinearMap.range (Module.Dual.eval Γ(X, c.chart.openSet)
    ((cartierDivisorModule X D).val.obj (op c.chart.openSet)) _) = _
  rw [dual_evaluation_range_eq_span
    (cartierEquationSectionEquiv X D c.chart.openSet c.chart.equation
      c.chart.represents).symm, effectiveCartierSection_coordinate]

/-- The original over-site Cartier frame evaluates the canonical
section to the same regular equation, using its actual identity restriction. -/
theorem effectiveCartierSection_frame_eval (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (c : RegularCartierEquationChart X D) :
    KltDP.SheafOfModules.evalSection X.ringCatSheaf (cartierDivisorModule X D)
      c.chart.openSet
      (cartierEquationOverIso X D c.chart.openSet c.chart.equation c.chart.represents).inv
      ((cartierDivisorModule X D).val.map
        (homOfLE (le_top : c.chart.openSet ≤ ⊤)).op (effectiveCartierSection X D hD)) =
      c.coefficient := by
  let M : X.Modules := cartierDivisorModule X D
  let U : X.Opens := c.chart.openSet
  letI : Nonempty U := c.chart.nonempty
  letI : Nonempty (Over.mk (𝟙 U) : Over U).left := c.chart.nonempty
  let s : M.val.obj (op U) :=
    M.val.map (homOfLE (le_top : U ≤ ⊤)).op (effectiveCartierSection X D hD)
  let E : Γ(X, U) ≃ₗ[Γ(X, U)] M.val.obj (op U) :=
    cartierEquationSectionEquivOn X D U c.chart.equation c.chart.represents
      (Over.mk (𝟙 U))
  let τ : _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U :=
    cartierEquationOverIso X D U c.chart.equation c.chart.represents
  have hs : s = E c.coefficient := by
    refine (effectiveCartierSection_eq_equation_frame X D hD c).trans ?_
    apply Subtype.ext
    apply (rationalFunctionModuleSectionsEquiv X U).injective
    exact (cartierEquationSectionEquiv_apply_field X D U
      c.chart.equation c.chart.represents c.coefficient).trans
      (cartierEquationSectionEquivOn_apply_field X D U c.chart.equation
        c.chart.represents (Over.mk (𝟙 U)) c.coefficient).symm
  have hτ : τ.hom.val.app (op (Over.mk (𝟙 U))) c.coefficient = E c.coefficient := rfl
  have hid : M.val.map (𝟙 U).op s = s :=
    CategoryTheory.congr_fun (M.val.presheaf.map_id (op U)) s
  have hcancel : τ.inv.val.app (op (Over.mk (𝟙 U)))
      (τ.hom.val.app (op (Over.mk (𝟙 U))) c.coefficient) = c.coefficient :=
    congrArg
      (fun f : _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
          _root_.SheafOfModules.unit (X.ringCatSheaf.over U) =>
        f.val.app (op (Over.mk (𝟙 U))) c.coefficient)
      τ.hom_inv_id
  have hc : τ.inv.val.app (op (Over.mk (𝟙 U))) (M.val.map (𝟙 U).op s) =
      c.coefficient :=
    (congrArg (fun t : M.val.obj (op U) => τ.inv.val.app (op (Over.mk (𝟙 U))) t)
      (hid.trans (hs.trans hτ.symm))).trans hcancel
  exact (KltDP.SheafOfModules.evalSection_eq X.ringCatSheaf M U τ.inv s).trans hc

/-- The component image of the genuine sheaf-dual evaluation has the
original Cartier equation ideal; no image identification is assumed. -/
theorem effectiveCartierSection_evaluationMorphism_range (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (c : RegularCartierEquationChart X D) :
    LinearMap.range ((sectionEvaluationMorphism X (cartierDivisorModule X D)
      (effectiveCartierSection X D hD)).val.app (op c.chart.openSet)).hom =
      Ideal.span ({c.coefficient} : Set Γ(X, c.chart.openSet)) := by
  rw [sectionEvaluationMorphism_range_eq_span X (cartierDivisorModule X D)
    (effectiveCartierSection X D hD) c.chart.openSet
    (cartierEquationOverIso X D c.chart.openSet c.chart.equation c.chart.represents).symm,
    Iso.symm_hom, effectiveCartierSection_frame_eval X D hD c]

local instance effectiveCartierMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- With an original square-root isomorphism, the genuine categorical
image ideal has the prescribed Cartier equation on every regular chart.
The nonzero section needed by the preceding image comparison is derived. -/
theorem effectiveCartierSection_imageIdeal [X.IsSeparated] (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (L : InvertibleSheaf X)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X D)
    (c : RegularCartierEquationChart X D) :
    sectionImageIdeal X (cartierDivisorModule X D) (effectiveCartierSection X D hD)
      c.chart.openSet = Ideal.span ({c.coefficient} : Set Γ(X, c.chart.openSet)) := by
  rw [InvertibleQuadraticAtlas.sectionImageIdeal_eq_componentRange_of_nonzero X
    (cartierDivisorModule X D) (effectiveCartierSection X D hD) L e
    (effectiveCartierSection_ne_zero X D hD) c.chart.openSet,
    effectiveCartierSection_evaluationMorphism_range]

end KltDP.Geometry
