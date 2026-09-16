import KltDP.Geometry.InvertibleSheafSectionPowersPullback
import KltDP.Geometry.InvertibleSheafPowerFrameTransition

/-!
# Actual power frames commute with original pullback

The pulled original frame has the pulled original frame generator. The already
proved power-section pullback identity, applied to this generator, identifies
the inverse power frames. Cancelling the actual isomorphisms gives the desired
power-frame comparison. The coefficient of every original section is also
transported by the literal structural section map.

This reuses the original power and pullback comparisons, including their proved
unit and tensor compatibility; no monoidal compatibility is assumed. The frame
is an explicit actual sheaf isomorphism, as on a trivializing chart. These are
overlap-transport identities, not a global extension or ampleness theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.InvertibleSheafPowerFramePullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance framePullbackMonoidal (Z : Scheme.{u}) : MonoidalCategory Z.Modules :=
  Scheme.Modules.monoidalCategory Z

open InvertibleSheafSectionPowers InvertibleSheafSectionPowersPullback
open InvertibleSheafPowerFrameTransition RationalTreePicard

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (L : InvertibleSheaf X)
  (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)

/-- Pull the actual frame through the actual functor and its structure-unit comparison. -/
def pullbackFrame : (pullbackInvertibleSheaf f L).obj ≅
    _root_.SheafOfModules.unit Y.ringCatSheaf :=
  (schemeModulePullback f).mapIso e ≪≫ schemeModulePullbackUnitIso f

/-- The pulled frame generator is the original adjunction-unit pullback
of the original frame generator. -/
theorem pullback_frameGenerator :
    InvertibleSheafSectionPowersPullback.pullbackSection f L.obj (frameGenerator L e) =
      frameGenerator (pullbackInvertibleSheaf f L) (pullbackFrame f L e) := by
  simp only [InvertibleSheafSectionPowersPullback.pullbackSection, frameGenerator, Equiv.symm_apply_apply,
    pullbackFrame, Iso.trans_inv, Functor.mapIso_inv]
  rfl

set_option maxHeartbeats 800000 in
/-- The original power/pullback comparison carries the original pulled
power frame to the power of the original pulled frame. -/
theorem powerFrame_pullback (n : ℕ) :
    (powerPullbackIso f L n).hom ≫
        (powerFrame (pullbackInvertibleSheaf f L) (pullbackFrame f L e) n).hom =
      (schemeModulePullback f).map (powerFrame L e n).hom ≫
        (schemeModulePullbackUnitIso f).hom := by
  let a := (schemeModulePullback f).mapIso (powerFrame L e n) ≪≫
    schemeModulePullbackUnitIso f
  have h := powerSectionHom_pullback f L (frameGenerator L e) n
  simp only [pullback_frameGenerator, powerSectionHom_frameGenerator] at h
  have ha : a.inv ≫ (powerPullbackIso f L n).hom =
      (powerFrame (pullbackInvertibleSheaf f L) (pullbackFrame f L e) n).inv := h
  have h' := congrArg (fun g => a.hom ≫ g ≫
    (powerFrame (pullbackInvertibleSheaf f L) (pullbackFrame f L e) n).hom) ha
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h'

/-- The pulled frame coefficient of any actual compatible section is
the original coefficient through the original structural section map. -/
theorem frameCoefficient_pullback (s : L.obj.sections) :
    frameCoefficient (pullbackInvertibleSheaf f L) (pullbackFrame f L e)
        (InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s) =
      f.app ⊤ (frameCoefficient L e s) := by
  have hs := pullbackSection_val f L.obj s (⊤ : X.Opens)
  have hm := pullback_map_val_app_pulledSection f e.hom (⊤ : X.Opens) (s.val (op ⊤))
  have hu := unitIso_hom_val_app_pulledSection f (⊤ : X.Opens) (frameCoefficient L e s)
  change (schemeModulePullbackUnitIso f).hom.val.app (op (f ⁻¹ᵁ (⊤ : X.Opens)))
      (((schemeModulePullback f).map e.hom).val.app (op (f ⁻¹ᵁ (⊤ : X.Opens)))
        ((InvertibleSheafSectionPowersPullback.pullbackSection f L.obj s).val (op (f ⁻¹ᵁ (⊤ : X.Opens))))) = _
  exact (congrArg (fun z => (schemeModulePullbackUnitIso f).hom.val.app
    (op (f ⁻¹ᵁ (⊤ : X.Opens)))
      (((schemeModulePullback f).map e.hom).val.app (op (f ⁻¹ᵁ (⊤ : X.Opens))) z)) hs).trans
    ((congrArg ((schemeModulePullbackUnitIso f).hom.val.app
      (op (f ⁻¹ᵁ (⊤ : X.Opens)))) hm).trans hu)

end KltDP.Geometry.InvertibleSheafPowerFramePullback
