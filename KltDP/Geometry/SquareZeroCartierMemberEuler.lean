import KltDP.Geometry.CanonicalEulerDefectVanishes
import KltDP.Geometry.CartierEulerPairingEffective
import KltDP.Geometry.CartierPrincipalPicard

/-! Arithmetic adjunction for an actual effective Cartier scheme, including
possibly reducible or nonreduced members. Original RR and the proved ideal
sequence give its Euler value; no integrality or surface Euler assumption
is used. The square-zero fiber class has Euler characteristic exactly one. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance memberEulerSourceIntegral : IsIntegral X.toScheme := X.integral

include eK in
/-- The arithmetic adjunction identity for any original effective Cartier
subscheme presented by its actual closed immersion and ideal. -/
theorem effectiveCartier_twice_euler_of_ker
    (E : CartierDivisor X.toScheme) (hE : HasRegularCartierEquations X.toScheme E)
    {Z : Scheme.{u}} (i : Z ⟶ X.toScheme) [IsClosedImmersion i]
    (hi : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme E hE) :
    2 * eulerCharacteristic (i ≫ X.structureMorphism)
      (_root_.SheafOfModules.unit Z.ringCatSheaf) =
        -(X.intersectionPairing hX E E + X.intersectionPairing hX K E) := by
  have hr := X.cartier_euler_riemannRoch_twice hX K eK (-E)
  have he := X.eulerCharacteristic_unit_sub_neg_of_ker E hE i hi
  have hp : X.intersectionPairing hX (-E) ((-E) - K) =
      X.intersectionPairing hX E E + X.intersectionPairing hX K E := by
    rw [show (-E) - K = -(E + K) by abel,
      X.intersectionPairing_neg_left, X.intersectionPairing_neg_right, neg_neg,
      X.intersectionPairing_add_right, X.intersectionPairing_symm hX E K]
  rw [hp] at hr
  omega

include eK in
/-- Every original effective Cartier member of the square-zero class has
Euler characteristic one, retaining the complete original closed scheme. -/
theorem squareZero_member_eulerCharacteristic_eq_one
    (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (E : CartierDivisor X.toScheme) (hE : HasRegularCartierEquations X.toScheme E)
    (e : cartierDivisorModule X.toScheme E ≅ cartierDivisorModule X.toScheme F)
    {Z : Scheme.{u}} (i : Z ⟶ X.toScheme) [IsClosedImmersion i]
    (hi : i.ker = effectiveCartierIdealDataOfRegularEquations X.toScheme E hE) :
    eulerCharacteristic (i ≫ X.structureMorphism)
      (_root_.SheafOfModules.unit Z.ringCatSheaf) = 1 := by
  have hc := cartierPicardClass_eq_of_iso X.toScheme E F e
  have hEE : X.intersectionPairing hX E E = 0 := by
    rw [← X.picardPairing_class hX E E, hc, X.picardPairing_class, hFF]
  have hKE : X.intersectionPairing hX K E = -2 := by
    rw [← X.picardPairing_class hX K E, hc, X.picardPairing_class, hKF]
  have h := X.effectiveCartier_twice_euler_of_ker hX K eK E hE i hi
  rw [hEE, hKE] at h
  omega

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_member_eulerCharacteristic_eq_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_member_eulerCharacteristic_eq_one
