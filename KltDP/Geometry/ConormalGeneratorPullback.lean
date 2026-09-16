import KltDP.Geometry.SchemeConormalEquationChange

/-!
# Transport of the original conormal equation maps

An arbitrary actual scheme morphism pulls an original conormal equation
map back to a map from its own structure module, using the same canonical
pullback-unit normalization. Multipliers are transported by the original
composite section map. If the equation regularly generates the actual
kernel on an affine target, the transported map is an actual frame.

This supplies the frame-preserving operation needed when the original
exceptional scheme is identified with its actual fiber and with P1.
No chosen frame, transition equation, or invertibility conclusion is an
input to the regular-principal specialization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ X)

/-- The actual original equation map, transported along an actual
scheme morphism with the canonical source-unit normalization. -/
def pulledConormalGenerator (d : Γ(Y, ⊤)) (hd : f.appTop d = 0) :
    _root_.SheafOfModules.unit Z.ringCatSheaf ⟶
      (schemeModulePullback g).obj (schemeConormalSheaf f) :=
  (schemeModulePullbackUnitIso g).inv ≫
    (schemeModulePullback g).map (schemeConormalGenerator f d hd)

/-- Original equation multipliers become the actual composite section
map's multipliers after transport of the conormal map. -/
theorem pulledConormalGenerator_mul (r d : Γ(Y, ⊤)) (hd : f.appTop d = 0) :
    pulledConormalGenerator f g (r * d) (schemeEquation_mul_eq_zero f r d hd) =
      schemeScalarEnd ((g ≫ f).appTop r) ≫ pulledConormalGenerator f g d hd := by
  change (schemeModulePullbackUnitIso g).inv ≫
      (schemeModulePullback g).map
        (schemeConormalGenerator f (r * d) (schemeEquation_mul_eq_zero f r d hd)) =
    schemeScalarEnd (g.appTop (f.appTop r)) ≫
      (schemeModulePullbackUnitIso g).inv ≫
        (schemeModulePullback g).map (schemeConormalGenerator f d hd)
  rw [schemeConormalGenerator_mul f r d hd, Functor.map_comp, ← Category.assoc,
    schemeModulePullbackUnitIso_inv_scalar g (f.appTop r), Category.assoc]

variable (d : Γ(Y, ⊤)) (hd : f.appTop d = 0) [IsAffine Y] [QuasiCompact f]
  (hker : RingHom.ker f.appTop.hom = Ideal.span {d})
  (hregular : d ∈ nonZeroDivisors Γ(Y, ⊤))

include hker hregular in
/-- Literal regular generation of the actual affine section kernel
makes the transported original equation map an isomorphism. -/
theorem pulledConormalGenerator_isIso :
    IsIso (pulledConormalGenerator f g d hd) := by
  letI := schemeKernelGenerator_isIso f d hd hker hregular
  change IsIso ((schemeModulePullbackUnitIso g).inv ≫
    (schemeModulePullback g).map
      ((schemeModulePullbackUnitIso f).inv ≫
        (schemeModulePullback f).map (schemeKernelGenerator f d hd)))
  infer_instance

/-- The transported frame retains exactly the original equation map. -/
def pulledConormalFrameIso :
    _root_.SheafOfModules.unit Z.ringCatSheaf ≅
      (schemeModulePullback g).obj (schemeConormalSheaf f) := by
  letI := pulledConormalGenerator_isIso f g d hd hker hregular
  exact asIso (pulledConormalGenerator f g d hd)

/-- No new basis is chosen when packaging the transported frame. -/
theorem pulledConormalFrameIso_hom :
    (pulledConormalFrameIso f g d hd hker hregular).hom =
      pulledConormalGenerator f g d hd := rfl

end KltDP.Geometry
