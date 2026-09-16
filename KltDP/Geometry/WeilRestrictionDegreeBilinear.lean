import KltDP.AdmissionProbe.CurveTensorDegreeConsumers
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Ordinary integral bilinearity at the actual divisor use site

INACTIVE TEXT. This consumer requires the separately reviewed and admitted
full proper-cohomology and 0AYX inputs in its proposed import chain.
It declares no literature input or assumed degree/intersection law.

The functions and all their values are the existing actual restriction
degrees. The proved Cartier-to-Picard map transports tensor additivity to
the original Cartier divisor variable. The proved regular Cartier-Weil
inverse then supplies the regular-Weil variable. This establishes the
integral bilinearity clause of F03 for restriction degree; the other
intersection and numerical-quotient clauses require separate results.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry
open KltDP.AdmissionProbe.CurveTensorDegreeConsumers
open scoped BigOperators

universe u

namespace KltDP.AdmissionProbe.WeilRestrictionDegreeBilinear

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The original Cartier restriction-degree function is integer-linear in
both actual divisor arguments. The geometric first-variable law is inherited
through the actual O(D) Picard homomorphism. -/
def cartierWeilRestrictionBilinear :
    CartierDivisor X.toScheme →ₗ[ℤ] X.WeilDivisor →ₗ[ℤ] ℤ :=
  ((picardWeilRestrictionDegreeHom X).comp (cartierPicardHom X.toScheme)).toIntLinearMap

/-- Bundling retains exactly the previously defined degree values. -/
@[simp]
theorem cartierWeilRestrictionBilinear_apply (D : CartierDivisor X.toScheme) :
    cartierWeilRestrictionBilinear X D = X.cartierWeilRestrictionDegree D := rfl

/-- The unchanged actual Cartier degree adds in its first divisor argument. -/
theorem cartierWeilRestrictionDegree_add (D E : CartierDivisor X.toScheme) :
    X.cartierWeilRestrictionDegree (D + E) =
      X.cartierWeilRestrictionDegree D + X.cartierWeilRestrictionDegree E :=
  (cartierWeilRestrictionBilinear X).map_add D E

/-- The original rational function's principal Cartier divisor has zero form. -/
@[simp]
theorem cartierWeilRestrictionBilinear_principal (f : X.toScheme.functionFieldˣ) :
    cartierWeilRestrictionBilinear X
      (principalCartierDivisorHom X.toScheme (Additive.ofMul f)) = 0 :=
  X.cartierWeilRestrictionDegree_principal f

section Regular

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The same form on original Weil divisors, transported through the proved
Cartier inverse on the original regular surface. No symmetry is included. -/
def regularWeilRestrictionBilinear :
    X.WeilDivisor →ₗ[ℤ] X.WeilDivisor →ₗ[ℤ] ℤ :=
  (cartierWeilRestrictionBilinear X).comp
    (X.regularCartierWeilEquiv hregular).symm.toIntLinearEquiv.toLinearMap

/-- The original regular-Weil degree function is unchanged by this bundling. -/
@[simp]
theorem regularWeilRestrictionBilinear_apply (D : X.WeilDivisor) :
    regularWeilRestrictionBilinear X hregular D =
      X.regularWeilRestrictionDegree hregular D :=
  (X.regularWeilRestrictionDegree_eq_cartier hregular D).symm

/-- The previous actual degree function now has its first-variable additive law. -/
theorem regularWeilRestrictionDegree_add (D E : X.WeilDivisor) :
    X.regularWeilRestrictionDegree hregular (D + E) =
      X.regularWeilRestrictionDegree hregular D +
        X.regularWeilRestrictionDegree hregular E := by
  simpa only [regularWeilRestrictionBilinear_apply] using
    (regularWeilRestrictionBilinear X hregular).map_add D E

/-- Evaluation retains the original O(D) pullback on every original prime curve. -/
theorem regularWeilRestrictionBilinear_eq_euler (D Z : X.WeilDivisor) :
    regularWeilRestrictionBilinear X hregular D Z =
      ∑ C ∈ Z.support, Z C *
        (ModuleCohomology.eulerCharacteristic C.toSpec
          ((schemeModulePullback C.inclusion).obj
            (cartierDivisorModule X.toScheme
              ((X.regularCartierWeilEquiv hregular).symm D))) -
        ModuleCohomology.eulerCharacteristic C.toSpec
          (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf)) :=
  X.cartierWeilRestrictionDegree_apply
    ((X.regularCartierWeilEquiv hregular).symm D) Z

end Regular

end KltDP.AdmissionProbe.WeilRestrictionDegreeBilinear
