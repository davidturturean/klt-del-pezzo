import KltDP.Geometry.PrincipalKernelSheaf
import KltDP.Geometry.SchemeModuleFunctorial

/-!
# Actual conormal frames under a change of local equation

Multiplying an equation d by a function r multiplies the actual kernel
frame by r. Pullback transports this to multiplication by the original
section map's image of r on the conormal frame. The scalar comparison
is proved from the original pullback/pushforward adjunction.

The equations need only be killed by the actual scheme morphism. No
regularity, affine hypothesis, invertibility, or transition formula is
assumed. Restricting these statements to common chart opens gives the
equation-change part of the conormal transition comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}}

/-- Multiplication of functions is composition of the original scalar
endomorphisms of the actual structure module. -/
theorem schemeScalarEnd_mul (r d : Γ(Y, ⊤)) :
    schemeScalarEnd (r * d) = schemeScalarEnd r ≫ schemeScalarEnd d := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let s' : Γ(Y, V.unop) := s
  change s' * Y.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op (r * d) =
    (s' * Y.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op r) *
      Y.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op d
  rw [(Y.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op).hom.map_mul,
    mul_assoc]

variable (f : X ⟶ Y)

/-- The actual structure map intertwines multiplication by a function
with multiplication by its original image on the source. -/
theorem schemeScalarEnd_structure (r : Γ(Y, ⊤)) :
    schemeScalarEnd r ≫ structureToPushforwardUnit f =
      structureToPushforwardUnit f ≫
        (schemeModulePushforward f).map (schemeScalarEnd (f.appTop r)) := by
  apply (((schemeModulePushforward f).obj
    (_root_.SheafOfModules.unit X.ringCatSheaf)).unitHomEquiv).injective
  apply (schemeModuleSectionsEquivTop _).injective
  change f.appTop ((schemeScalarEnd r).val.app (op ⊤) (1 : Γ(Y, ⊤))) =
    (schemeScalarEnd (f.appTop r)).val.app (op (f ⁻¹ᵁ ⊤)) (f.appTop (1 : Γ(Y, ⊤)))
  simp only [Opens.map_top, schemeScalarEnd_appTop, one_mul, f.appTop.hom.map_one]

/-- The canonical pullback-unit map transports the original scalar action. -/
theorem schemeModulePullbackUnitHom_scalar (r : Γ(Y, ⊤)) :
    (schemeModulePullback f).map (schemeScalarEnd r) ≫ schemeModulePullbackUnitHom f =
      schemeModulePullbackUnitHom f ≫ schemeScalarEnd (f.appTop r) := by
  let a := _root_.SheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f)
  apply (a.homEquiv _ _).injective
  calc
    _ = schemeScalarEnd r ≫ a.homEquiv _ _ (schemeModulePullbackUnitHom f) :=
      a.homEquiv_naturality_left (schemeScalarEnd r) (schemeModulePullbackUnitHom f)
    _ = schemeScalarEnd r ≫ structureToPushforwardUnit f := by
      rw [schemeModulePullbackUnitHom_adjunction]
    _ = structureToPushforwardUnit f ≫
        (schemeModulePushforward f).map (schemeScalarEnd (f.appTop r)) :=
      schemeScalarEnd_structure f r
    _ = a.homEquiv _ _
        (schemeModulePullbackUnitHom f ≫ schemeScalarEnd (f.appTop r)) := by
      rw [a.homEquiv_naturality_right, schemeModulePullbackUnitHom_adjunction]
      rfl

/-- Inverse unit transport has the same actual scalar normalization. -/
theorem schemeModulePullbackUnitIso_inv_scalar (r : Γ(Y, ⊤)) :
    (schemeModulePullbackUnitIso f).inv ≫
        (schemeModulePullback f).map (schemeScalarEnd r) =
      schemeScalarEnd (f.appTop r) ≫ (schemeModulePullbackUnitIso f).inv := by
  have h : (schemeModulePullback f).map (schemeScalarEnd r) ≫
      (schemeModulePullbackUnitIso f).hom =
    (schemeModulePullbackUnitIso f).hom ≫ schemeScalarEnd (f.appTop r) :=
    schemeModulePullbackUnitHom_scalar f r
  have h' := congrArg (fun g =>
    (schemeModulePullbackUnitIso f).inv ≫ g ≫ (schemeModulePullbackUnitIso f).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using h'

variable (r d : Γ(Y, ⊤)) (hd : f.appTop d = 0)

include hd in
/-- The product equation is killed by the actual section map. -/
theorem schemeEquation_mul_eq_zero : f.appTop (r * d) = 0 := by
  rw [f.appTop.hom.map_mul, hd, mul_zero]

/-- The actual categorical-kernel generator changes by the original scalar map. -/
theorem schemeKernelGenerator_mul :
    schemeKernelGenerator f (r * d) (schemeEquation_mul_eq_zero f r d hd) =
      schemeScalarEnd r ≫ schemeKernelGenerator f d hd := by
  apply (cancel_mono (kernel.ι (structureToPushforwardUnit f))).mp
  change schemeKernelGenerator f (r * d) (schemeEquation_mul_eq_zero f r d hd) ≫
      schemeKernelIdealι f =
    (schemeScalarEnd r ≫ schemeKernelGenerator f d hd) ≫ schemeKernelIdealι f
  rw [Category.assoc, schemeKernelGenerator_comp_ι, schemeKernelGenerator_comp_ι]
  exact schemeScalarEnd_mul r d

/-- The actual conormal equation map, with source unit normalized by
the original adjunction. It is a frame when the regular-generator
conditions are separately proved. -/
def schemeConormalGenerator (d : Γ(Y, ⊤)) (hd : f.appTop d = 0) :
    _root_.SheafOfModules.unit X.ringCatSheaf ⟶ schemeConormalSheaf f :=
  (schemeModulePullbackUnitIso f).inv ≫
    (schemeModulePullback f).map (schemeKernelGenerator f d hd)

/-- On actual conormal sheaves the transition multiplier is the image
of the equation multiplier under the original structural section map. -/
theorem schemeConormalGenerator_mul :
    schemeConormalGenerator f (r * d) (schemeEquation_mul_eq_zero f r d hd) =
      schemeScalarEnd (f.appTop r) ≫ schemeConormalGenerator f d hd := by
  change (schemeModulePullbackUnitIso f).inv ≫
      (schemeModulePullback f).map
        (schemeKernelGenerator f (r * d) (schemeEquation_mul_eq_zero f r d hd)) =
    schemeScalarEnd (f.appTop r) ≫ (schemeModulePullbackUnitIso f).inv ≫
      (schemeModulePullback f).map (schemeKernelGenerator f d hd)
  rw [schemeKernelGenerator_mul f r d hd, Functor.map_comp, ← Category.assoc,
    schemeModulePullbackUnitIso_inv_scalar f r, Category.assoc]

end KltDP.Geometry
