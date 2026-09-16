import KltDP.Geometry.InvertibleSheafTwistFrame

/-!
# Twisting is invertible on the original nonvanishing coefficient open

In an actual line-sheaf frame, the original twist map is bijective on
sections of every subopen of the original coefficient basic open. This
uses the literal coefficient unit supplied by the ringed-space basic-open
theorem. No quasicoherence, finite generation, or extension is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafTwistOnNonvanishing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance twistNonvanishingMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance originalSectionModule {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame

variable {X : Scheme.{u}}

/-- The original coefficient is a unit on every original subopen of D(a). -/
theorem isUnit_restrict_of_le_basicOpen (a : Γ(X, ⊤)) {V : X.Opens}
    (hV : V ≤ X.basicOpen a) :
    IsUnit (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op a) := by
  have hD : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
    RingedSpace.isUnit_res_basicOpen _ a
  have h := hD.map (X.presheaf.map (homOfLE hV).op).hom
  have heq : X.presheaf.map (homOfLE hV).op
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op a := by
    change (X.presheaf.map (homOfLE (X.basicOpen_le a)).op ≫
      X.presheaf.map (homOfLE hV).op) a = _
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  exact heq ▸ h

/-- The actual original twist map is bijective on every subopen on which
its frame coefficient is invertible, including degree zero. -/
theorem rightTwistMap_app_bijective (M : X.Modules) (L : InvertibleSheaf X)
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (s : L.obj.sections)
    (n : ℕ) {V : X.Opens} (hV : V ≤ X.basicOpen (frameCoefficient L e s)) :
    Function.Bijective ((rightTwistMap M L s n).val.app (op V)) := by
  let a : Γ(X, V) := X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
    (frameCoefficient L e s)
  have ha : IsUnit (a ^ n) := (isUnit_restrict_of_le_basicOpen (frameCoefficient L e s) hV).pow n
  let ε := ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op V)).mapIso
    (rightTwistFrame M L e n)).toLinearEquiv
  have hf (t : M.val.obj (op V)) :
      ε ((rightTwistMap M L s n).val.app (op V) t) = a ^ n • t := by
    simpa only [a, map_pow] using rightTwistMap_frame_apply M L e s n V t
  constructor
  · intro t v htv
    apply ha.smul_bijective.injective
    exact (hf t).symm.trans ((congrArg ε htv).trans (hf v))
  · intro t
    obtain ⟨v, hv⟩ := ha.smul_bijective.surjective (ε t)
    exact ⟨v, ε.injective ((hf v).trans hv)⟩

end KltDP.Geometry.InvertibleSheafTwistOnNonvanishing
