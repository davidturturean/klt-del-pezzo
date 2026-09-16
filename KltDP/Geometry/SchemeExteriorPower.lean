import KltDP.Compatibility.ExteriorPowerPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The exterior-power sheaf of an actual scheme module

This definition is independent of charts and frames. It sheafifies the
pointwise exterior powers over the original structure-section rings, with
restrictions induced by the original module restrictions. Exterior powers of
sections need not already form a sheaf, so sheafification is explicit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SchemeExteriorPower

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (M : X.Modules) (n : ℕ)

/-- The actual pointwise exterior-power presheaf. -/
abbrev presheaf : X.PresheafOfModules :=
  KltDP.Compatibility.ExteriorPowerPresheaf.presheaf X.presheaf M.val n

/-- The exterior power as an actual module sheaf, with no frame or cover input. -/
def sheaf : X.Modules :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj
    (presheaf M n)

/-- The actual sheafification unit on the exterior-power presheaf. -/
def toSheaf : presheaf M n ⟶ (sheaf M n).val :=
  (_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).unit.app (presheaf M n)

/-- A wedge of actual module sections, followed by the sheafification unit. -/
def wedge (W : X.Opens) :
    (M.val.obj (op W)) [⋀^Fin n]→ₗ[Γ(X, W)] ((sheaf M n).val.obj (op W)) :=
  ((toSheaf M n).app (op W)).hom.compAlternatingMap
    (exteriorPower.ιMulti Γ(X, W) n)

/-- The global wedge respects every original open restriction. -/
theorem wedge_restrict {V W : X.Opens} (h : V ≤ W)
    (v : Fin n → M.val.obj (op W)) :
    (sheaf M n).val.map (homOfLE h).op (wedge M n W v) =
      wedge M n V (fun i => M.val.map (homOfLE h).op (v i)) := by
  change (sheaf M n).val.map (homOfLE h).op
      ((toSheaf M n).app (op W) (exteriorPower.ιMulti Γ(X, W) n v)) = _
  rw [← _root_.PresheafOfModules.naturality_apply]
  exact congrArg ((toSheaf M n).app (op V))
    (KltDP.Compatibility.ExteriorPowerPresheaf.presheaf_map_mk
      X.presheaf M.val n (homOfLE h).op v)

/-- The exterior sheaf has the original sheafification universal property. -/
def homEquiv (N : X.Modules) :
    (sheaf M n ⟶ N) ≃ (presheaf M n ⟶ N.val) :=
  _root_.PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.val)

end KltDP.Geometry.SchemeExteriorPower
