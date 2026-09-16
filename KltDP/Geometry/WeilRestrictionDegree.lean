import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.RegularSurfaceWeilPicard

/-!
# Finite Weil extension of actual restriction degree

For each original surface Picard class, extend its actual prime-curve
restriction degrees using the already established finite Weil decomposition.
The output is linear in the Weil curve variable. The Picard, Cartier, and
regular-Weil first arguments are functions, without an additivity claim.

The Cartier formula computes the original pullback of the existing O(D)
module, with each curve's original scalar action. The regular-Weil formula
uses the existing proved Cartier inverse, and linear equivalence in that
first variable follows from its actual Picard class. No numerical
intersection, tensor additivity of degree, or symmetry is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The actual restriction degree is extended along the existing finite
prime decomposition. Only the Weil curve variable is bundled as linear. -/
def picardWeilRestrictionDegree (p : X.toScheme.Pic) : X.WeilDivisor →ₗ[ℤ] ℤ :=
  divisorLinearExtension (fun C : X.PrimeCurve => C.picardRestrictionDegree p)

/-- Every actual prime coefficient weights its own intrinsic restriction
degree. This is the existing finite support, not a chosen decomposition. -/
theorem picardWeilRestrictionDegree_apply (p : X.toScheme.Pic) (Z : X.WeilDivisor) :
    X.picardWeilRestrictionDegree p Z =
      ∑ C ∈ Z.support, Z C * C.picardRestrictionDegree p := by
  simp only [picardWeilRestrictionDegree, divisorLinearExtension_apply,
    zsmul_eq_mul, Int.cast_id]

/-- On a single prime curve the finite extension recovers restriction
degree with its actual integral multiplicity. -/
@[simp]
theorem picardWeilRestrictionDegree_single (p : X.toScheme.Pic)
    (C : X.PrimeCurve) (a : ℤ) :
    X.picardWeilRestrictionDegree p (Finsupp.single C a) =
      a * C.picardRestrictionDegree p := by
  simp only [picardWeilRestrictionDegree, divisorLinearExtension_single,
    zsmul_eq_mul, Int.cast_id]

/-- The trivial surface Picard class gives the zero linear form on the
actual finite Weil divisors. -/
@[simp]
theorem picardWeilRestrictionDegree_one : X.picardWeilRestrictionDegree 1 = 0 := by
  apply LinearMap.ext
  intro Z
  simp only [picardWeilRestrictionDegree_apply, PrimeCurve.picardRestrictionDegree_one,
    mul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

/-- On the class of an actual line bundle the coefficients are the
degrees of its actual restrictions to the actual curve schemes. -/
theorem picardWeilRestrictionDegree_toPic
    (L : InvertibleSheaf X.toScheme) (Z : X.WeilDivisor) :
    X.picardWeilRestrictionDegree L.toPic Z =
      ∑ C ∈ Z.support, Z C * C.restrictionDegree L := by
  simp only [picardWeilRestrictionDegree_apply, PrimeCurve.picardRestrictionDegree_toPic]

/-- Original coefficient-sheaf isomorphisms preserve the entire finite
restriction-degree linear form. -/
theorem picardWeilRestrictionDegree_eq_of_iso
    {L M : InvertibleSheaf X.toScheme} (e : L.obj ≅ M.obj) :
    X.picardWeilRestrictionDegree L.toPic = X.picardWeilRestrictionDegree M.toPic := by
  apply LinearMap.ext
  intro Z
  rw [X.picardWeilRestrictionDegree_toPic, X.picardWeilRestrictionDegree_toPic]
  apply Finset.sum_congr rfl
  intro C hC
  rw [C.restrictionDegree_eq_of_iso e]

/-- The finite restriction-degree form of the original Cartier O(D). -/
def cartierWeilRestrictionDegree (D : CartierDivisor X.toScheme) :
    X.WeilDivisor →ₗ[ℤ] ℤ :=
  X.picardWeilRestrictionDegree (cartierPicardClass X.toScheme D)

/-- The Cartier construction retains the original O(D), its actual
inclusion pullback, and each prime curve's original cohomology field action. -/
theorem cartierWeilRestrictionDegree_apply
    (D : CartierDivisor X.toScheme) (Z : X.WeilDivisor) :
    X.cartierWeilRestrictionDegree D Z =
      ∑ C ∈ Z.support, Z C *
        (ModuleCohomology.eulerCharacteristic C.toSpec
          ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) -
        ModuleCohomology.eulerCharacteristic C.toSpec
          (_root_.SheafOfModules.unit C.toScheme.ringCatSheaf)) := by
  change X.picardWeilRestrictionDegree (cartierDivisorInvertibleSheaf X.toScheme D).toPic Z = _
  rw [X.picardWeilRestrictionDegree_toPic]
  apply Finset.sum_congr rfl
  intro C hC
  rw [C.restrictionDegree_eq_euler]
  rfl

/-- An actual principal Cartier divisor restricts to a trivial line on
each curve, hence its finite restriction-degree form is zero. -/
@[simp]
theorem cartierWeilRestrictionDegree_principal (f : X.toScheme.functionFieldˣ) :
    X.cartierWeilRestrictionDegree
      (principalCartierDivisorHom X.toScheme (Additive.ofMul f)) = 0 := by
  unfold cartierWeilRestrictionDegree
  rw [cartierPicardClass_principal, X.picardWeilRestrictionDegree_one]

/-- Equality in the original Cartier class group preserves restriction
degree, by the proved Cartier-class-to-Picard map. -/
theorem cartierWeilRestrictionDegree_eq_of_class_eq
    {D E : CartierDivisor X.toScheme}
    (h : cartierClassMap X.toScheme D = cartierClassMap X.toScheme E) :
    X.cartierWeilRestrictionDegree D = X.cartierWeilRestrictionDegree E := by
  have hp : cartierPicardClass X.toScheme D = cartierPicardClass X.toScheme E := by
    simpa only [cartierClassToPicard_class] using
      congrArg (fun c => (cartierClassToPicard X.toScheme c).toMul) h
  unfold cartierWeilRestrictionDegree
  rw [hp]

section Regular

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- On the existing regular-surface realization, an actual Weil divisor
supplies its original sheaf Picard class in the first variable. -/
def regularWeilRestrictionDegree (D : X.WeilDivisor) : X.WeilDivisor →ₗ[ℤ] ℤ :=
  X.picardWeilRestrictionDegree (X.regularWeilPicardClass hregular D)

/-- The regular-Weil construction is exactly the restriction-degree form
of the existing Cartier inverse representative's original O(D). -/
theorem regularWeilRestrictionDegree_eq_cartier (D : X.WeilDivisor) :
    X.regularWeilRestrictionDegree hregular D =
      X.cartierWeilRestrictionDegree ((X.regularCartierWeilEquiv hregular).symm D) := by
  unfold regularWeilRestrictionDegree regularWeilPicardClass cartierWeilRestrictionDegree
  rw [X.regularWeilClassPicardEquiv_representative hregular D]

/-- The actual Cartier-to-Weil image retains the original Cartier
restriction-degree form. -/
theorem regularWeilRestrictionDegree_of_cartier (D : CartierDivisor X.toScheme) :
    X.regularWeilRestrictionDegree hregular (X.cartierToWeilHom D) =
      X.cartierWeilRestrictionDegree D := by
  unfold regularWeilRestrictionDegree regularWeilPicardClass cartierWeilRestrictionDegree
  rw [X.regularWeilClassPicardEquiv_of_cartier hregular D]

/-- The original Weil principal-divisor relation preserves the entire
restriction-degree form in the first variable. -/
theorem regularWeilRestrictionDegree_eq_of_linearlyEquivalent
    {D E : X.WeilDivisor} (h : X.LinearlyEquivalent D E) :
    X.regularWeilRestrictionDegree hregular D =
      X.regularWeilRestrictionDegree hregular E := by
  unfold regularWeilRestrictionDegree
  rw [(X.regularWeilPicardClass_eq_iff hregular D E).mpr h]

/-- Original principal Weil divisors have zero restriction-degree form. -/
@[simp]
theorem regularWeilRestrictionDegree_principal (f : X.toScheme.functionFieldˣ) :
    X.regularWeilRestrictionDegree hregular (X.principalDivisor f) = 0 := by
  unfold regularWeilRestrictionDegree
  rw [X.regularWeilPicardClass_principal hregular f, X.picardWeilRestrictionDegree_one]

end Regular

end KltDP.Geometry.NormalProjectiveSurface
