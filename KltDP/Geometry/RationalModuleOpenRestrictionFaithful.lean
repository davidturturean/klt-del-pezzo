import KltDP.Geometry.RationalModuleOpenRestriction
import KltDP.Geometry.ModuleRestrictionPullback

/-!
# Open restriction detects maps into the original rational-function module

On a nonempty open, original rational sections are the original function
field and restriction preserves that value. Any nonempty original open
immersion therefore detects equality of maps into this module, without a
local-freeness or extension premise on the source module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules)
    (α β : M ⟶ rationalFunctionModule X)

/-- Equality on the original image-open restriction implies equality on
all original opens, since their rational restriction maps are injective. -/
theorem hom_eq_of_restriction_eq
    (h : (SchemeModuleRestriction.restriction f).map α =
      (SchemeModuleRestriction.restriction f).map β) : α = β := by
  classical
  apply _root_.SheafOfModules.hom_ext
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  by_cases hU : Nonempty U.unop
  · letI := hU
    let W : Y.Opens := f ⁻¹ᵁ U.unop
    letI : Nonempty W := by
      refine ⟨⟨genericPoint Y, ?_⟩⟩
      change f.base (genericPoint Y) ∈ U.unop
      rw [genericPoint_eq_of_isOpenImmersion f]
      exact genericPoint_mem_nonempty_open X U.unop
    letI := nonempty_image f W
    let i : f ''ᵁ W ⟶ U.unop := homOfLE (by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact hy)
    have hvalue := congrArg
      (fun γ : (SchemeModuleRestriction.restriction f).obj M ⟶
          (SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X) =>
        γ.val.app (op W) (M.val.map i.op s)) h
    change α.val.app (op (f ''ᵁ W)) (M.val.map i.op s) =
      β.val.app (op (f ''ᵁ W)) (M.val.map i.op s) at hvalue
    have hres : (rationalFunctionModule X).val.map i.op (α.val.app U s) =
        (rationalFunctionModule X).val.map i.op (β.val.app U s) :=
      (_root_.PresheafOfModules.naturality_apply α.val i.op s).symm.trans
        (hvalue.trans (_root_.PresheafOfModules.naturality_apply β.val i.op s))
    apply (rationalFunctionModuleSectionsEquiv X U.unop).injective
    exact (rationalFunctionModuleSectionsEquiv_naturality X i (α.val.app U s)).symm.trans
      ((congrArg (rationalFunctionModuleSectionsEquiv X (f ''ᵁ W)) hres).trans
        (rationalFunctionModuleSectionsEquiv_naturality X i (β.val.app U s)))
  · letI := sectionRing_subsingleton_of_empty U.unop hU
    letI : Subsingleton ((rationalFunctionModule X).val.obj U) :=
      Module.subsingleton Γ(X, U.unop) _
    exact Subsingleton.elim _ _

/-- The same detection statement for the original scheme-module pullback,
using its accepted natural comparison with original open restriction. -/
theorem hom_eq_of_openPullback_eq
    (h : (schemeModulePullback f).map α = (schemeModulePullback f).map β) : α = β := by
  apply hom_eq_of_restriction_eq f M α β
  apply (cancel_mono ((SchemeModuleRestriction.restrictionIsoPullback f).hom.app
    (rationalFunctionModule X))).mp
  rw [(SchemeModuleRestriction.restrictionIsoPullback f).hom.naturality α,
    (SchemeModuleRestriction.restrictionIsoPullback f).hom.naturality β, h]

end KltDP.Geometry.OpenImmersionRational

#check @KltDP.Geometry.OpenImmersionRational.hom_eq_of_openPullback_eq
#print axioms KltDP.Geometry.OpenImmersionRational.hom_eq_of_openPullback_eq
