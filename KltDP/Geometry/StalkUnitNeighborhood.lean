import KltDP.Geometry.StalkCurveUnit
import Mathlib.Geometry.RingedSpace.Basic

/-!
# Actual regular units near a point

Pinned germ representability and the ringed-space local unit theorem
represent every stalk unit by an actual unit section on a neighborhood.
The original germ maps identify its image in the function field. Combined
with the curve-order criterion, equal local Weil orders give an actual
regular transition unit near each point.

No choice of a factorial affine neighborhood is used. The first two
lemmas use only pinned scheme/ringed-space definitions; the last theorem
assumes factoriality of the actual surface stalk.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Every actual stalk unit is the germ of an actual unit section on
some open neighborhood. -/
theorem exists_section_unit_of_stalk_unit (X : Scheme.{u}) (x : X)
    (a : (X.presheaf.stalk x)ˣ) :
    ∃ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)ˣ),
      Units.map (X.presheaf.germ U x hx).hom.toMonoidHom b = a := by
  obtain ⟨V, hxV, s, hs⟩ := X.presheaf.germ_exist x (a : X.presheaf.stalk x)
  have hunit : IsUnit (X.presheaf.germ V x hxV s) := by
    rw [hs]
    exact a.isUnit
  obtain ⟨U, i, hxU, hu⟩ :=
    X.toRingedSpace.isUnit_res_of_isUnit_germ V s x hxV hunit
  obtain ⟨b, hb⟩ := hu
  refine ⟨U, hxU, b, ?_⟩
  apply Units.ext
  change X.presheaf.germ U x hxU (b : Γ(X, U)) = (a : X.presheaf.stalk x)
  rw [hb]
  exact (X.presheaf.germ_res_apply i x hxU s).trans hs

/-- A stalk unit can be represented inside any specified open
neighborhood of its point. -/
theorem exists_section_unit_of_stalk_unit_within (X : Scheme.{u}) (x : X)
    (a : (X.presheaf.stalk x)ˣ) (U : X.Opens) (hxU : x ∈ U) :
    ∃ (V : X.Opens) (_ : V ≤ U) (hxV : x ∈ V) (b : Γ(X, V)ˣ),
      Units.map (X.presheaf.germ V x hxV).hom.toMonoidHom b = a := by
  obtain ⟨W, hxW, b, hb⟩ := exists_section_unit_of_stalk_unit X x a
  let V : X.Opens := W ⊓ U
  let c : Γ(X, V)ˣ := Units.map (X.presheaf.map (W.infLELeft U).op).hom.toMonoidHom b
  refine ⟨V, inf_le_right, ⟨hxW, hxU⟩, c, ?_⟩
  apply Units.ext
  change X.presheaf.germ V x ⟨hxW, hxU⟩
      (X.presheaf.map (W.infLELeft U).op (b : Γ(X, W))) = (a : X.presheaf.stalk x)
  exact (X.presheaf.germ_res_apply (W.infLELeft U) x ⟨hxW, hxU⟩ (b : Γ(X, W))).trans
    (congrArg (fun z : (X.presheaf.stalk x)ˣ => (z : X.presheaf.stalk x)) hb)

/-- Mapping a regular unit into the original function field agrees
with first taking its actual stalk germ. -/
theorem section_unit_toFunctionField_eq_stalk (X : Scheme.{u}) [IsIntegral X]
    (x : X) (U : X.Opens) [Nonempty U] (hx : x ∈ U) (b : Γ(X, U)ˣ) :
    Units.map (algebraMap (X.presheaf.stalk x) X.functionField)
        (Units.map (X.presheaf.germ U x hx).hom.toMonoidHom b) =
      Units.map (X.germToFunctionField U).hom.toMonoidHom b := by
  apply Units.ext
  change (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial))
      ((X.presheaf.germ U x hx) (b : Γ(X, U))) =
    (X.germToFunctionField U) (b : Γ(X, U))
  exact ConcreteCategory.congr_hom
    (X.presheaf.germ_stalkSpecializes hx ((genericPoint_spec X).specializes trivial))
      (b : Γ(X, U))

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- Equal curve orders near a point give an actual regular unit
representing the ratio on a smaller prescribed neighborhood. -/
theorem exists_regular_unit_near_of_equal_curve_orders (x : X.toScheme)
    [UniqueFactorizationMonoid (X.stalk x)]
    (U : X.toScheme.Opens) (hxU : x ∈ U) (f g : X.toScheme.functionFieldˣ)
    (horders : ∀ C : X.PrimeCurve, x ∈ C → C.order f = C.order g) :
    ∃ (V : X.toScheme.Opens) (_ : V ≤ U) (hxV : x ∈ V) (b : Γ(X.toScheme, V)ˣ),
      letI : Nonempty V := ⟨⟨x, hxV⟩⟩
      Units.map (X.toScheme.germToFunctionField V).hom.toMonoidHom b = f * g⁻¹ := by
  obtain ⟨a, ha⟩ := X.exists_stalk_unit_of_equal_curve_orders x f g horders
  obtain ⟨V, hVU, hxV, b, hb⟩ :=
    exists_section_unit_of_stalk_unit_within X.toScheme x a U hxU
  refine ⟨V, hVU, hxV, b, ?_⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  calc
    Units.map (X.toScheme.germToFunctionField V).hom.toMonoidHom b =
        Units.map (algebraMap (X.stalk x) X.toScheme.functionField)
          (Units.map (X.toScheme.presheaf.germ V x hxV).hom.toMonoidHom b) :=
      (section_unit_toFunctionField_eq_stalk X.toScheme x V hxV b).symm
    _ = f * g⁻¹ := by
      rw [hb]
      exact ha

end NormalProjectiveSurface

end KltDP.Geometry
