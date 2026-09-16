import KltDP.Geometry.CurveEffectiveCartierDegree
import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.NumericalEquivalence
import KltDP.Geometry.RegularSurfaceWeilPicard
import KltDP.Geometry.CartierPicardHom

/-!
# The intersection number `C·D` of a prime curve with an arbitrary Cartier divisor

`intersectionNumber C D := deg (i^*O_X(D))`, the degree on `C` of the pulled-back line bundle, is
defined for every Cartier divisor `D` on the surface (no support hypothesis; in particular for the
divisor of `C` itself on a regular surface, `selfIntersectionNumber`). It agrees with the
scheme-theoretic `intersectionDegree C D` when `C ⊄ Supp D` (Stacks 0AYY, task 12), is additive in
`D` and depends only on the Picard class of `O_X(D)` (through the admitted 0AYX additivity of the
degree on `C`), extends `ℤ`-linearly to the Cartier class group, and is the value of F02's
`picardRestrictionDegreeHom` at `C` on the class of `O_X(D)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)

/-- **The intersection number `C·D`** for an arbitrary Cartier divisor `D`: the degree of the
pulled-back line bundle `i^*O_X(D)` on `C`. -/
def intersectionNumber (D : CartierDivisor X.toScheme) : ℤ :=
  C.lineDegree (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D))

/-- The intersection number is the restriction degree of `O_X(D)`. -/
theorem intersectionNumber_eq_restrictionDegree (D : CartierDivisor X.toScheme) :
    C.intersectionNumber D = C.restrictionDegree (cartierDivisorInvertibleSheaf X.toScheme D) := rfl

/-- The intersection number is the Picard restriction degree of the class of `O_X(D)`. -/
theorem intersectionNumber_eq_picardRestrictionDegree (D : CartierDivisor X.toScheme) :
    C.intersectionNumber D = C.picardRestrictionDegree (cartierPicardClass X.toScheme D) :=
  (C.picardRestrictionDegree_toPic (cartierDivisorInvertibleSheaf X.toScheme D)).symm

/-- **Link with F02**: the restriction-degree homomorphism at `C`, evaluated on the additive Picard
class of `O_X(D)`, is `C·D`. -/
theorem picardRestrictionDegreeHom_cartierPicardHom (D : CartierDivisor X.toScheme) :
    X.picardRestrictionDegreeHom C (cartierPicardHom X.toScheme D) = C.intersectionNumber D := by
  rw [picardRestrictionDegreeHom_apply, cartierPicardHom_apply,
    C.intersectionNumber_eq_picardRestrictionDegree D]

/-- **Agreement with the scheme-theoretic intersection degree** off the support. -/
theorem intersectionNumber_eq_intersectionDegree (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D) (hC : C.NotInSupport D hD) :
    C.intersectionNumber D = (C.intersectionDegree D hD hC : ℤ) :=
  C.lineDegree_pullback_eq_intersectionDegree D hD hC

/-- **Additivity in the divisor** (admitted 0AYX). -/
theorem intersectionNumber_add (D₁ D₂ : CartierDivisor X.toScheme) :
    C.intersectionNumber (D₁ + D₂) = C.intersectionNumber D₁ + C.intersectionNumber D₂ := by
  rw [← C.picardRestrictionDegreeHom_cartierPicardHom (D₁ + D₂),
    ← C.picardRestrictionDegreeHom_cartierPicardHom D₁,
    ← C.picardRestrictionDegreeHom_cartierPicardHom D₂, map_add, map_add]

theorem intersectionNumber_zero : C.intersectionNumber 0 = 0 := by
  rw [← C.picardRestrictionDegreeHom_cartierPicardHom 0, map_zero, map_zero]

theorem intersectionNumber_neg (D : CartierDivisor X.toScheme) :
    C.intersectionNumber (-D) = -C.intersectionNumber D := by
  rw [← C.picardRestrictionDegreeHom_cartierPicardHom (-D),
    ← C.picardRestrictionDegreeHom_cartierPicardHom D, map_neg, map_neg]

/-- **Class dependence**: `C·D` depends only on the Picard class of `O_X(D)`. -/
theorem intersectionNumber_eq_of_cartierPicardClass_eq (D₁ D₂ : CartierDivisor X.toScheme)
    (h : cartierPicardClass X.toScheme D₁ = cartierPicardClass X.toScheme D₂) :
    C.intersectionNumber D₁ = C.intersectionNumber D₂ := by
  rw [C.intersectionNumber_eq_picardRestrictionDegree D₁,
    C.intersectionNumber_eq_picardRestrictionDegree D₂, h]

/-- Principal divisors have intersection number zero with every prime curve. -/
theorem intersectionNumber_principal (f : X.toScheme.functionFieldˣ) :
    C.intersectionNumber (principalCartierDivisorHom X.toScheme (Additive.ofMul f)) = 0 := by
  rw [← C.picardRestrictionDegreeHom_cartierPicardHom, cartierPicardHom_principal, map_zero]

/-- Adding a principal divisor does not change the intersection number. -/
theorem intersectionNumber_add_principal (D : CartierDivisor X.toScheme)
    (f : X.toScheme.functionFieldˣ) :
    C.intersectionNumber (D + principalCartierDivisorHom X.toScheme (Additive.ofMul f)) =
      C.intersectionNumber D := by
  rw [C.intersectionNumber_add, C.intersectionNumber_principal, add_zero]

/-- The intersection number as a homomorphism on Cartier divisors. -/
def intersectionNumberHom : CartierDivisor X.toScheme →+ ℤ :=
  (X.picardRestrictionDegreeHom C).comp (cartierPicardHom X.toScheme)

theorem intersectionNumberHom_apply (D : CartierDivisor X.toScheme) :
    C.intersectionNumberHom D = C.intersectionNumber D :=
  C.picardRestrictionDegreeHom_cartierPicardHom D

/-- **The `ℤ`-linear extension to the Cartier class group** (divisors modulo principal divisors). -/
def intersectionNumberClassHom : CartierClassGroup X.toScheme →+ ℤ :=
  (X.picardRestrictionDegreeHom C).comp (cartierClassToPicard X.toScheme)

theorem intersectionNumberClassHom_classMap (D : CartierDivisor X.toScheme) :
    C.intersectionNumberClassHom (cartierClassMap X.toScheme D) = C.intersectionNumber D := by
  show X.picardRestrictionDegreeHom C
    (((cartierClassToPicard X.toScheme).comp (cartierClassMap X.toScheme)) D) = _
  rw [cartierClassToPicard_comp_classMap]
  exact C.picardRestrictionDegreeHom_cartierPicardHom D

/-- **The self-intersection number `C·C`** on a regular surface over an algebraically closed field:
the intersection number of `C` with the Cartier divisor of the prime divisor `C`. -/
def selfIntersectionNumber [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) : ℤ :=
  C.intersectionNumber ((X.regularCartierWeilEquiv hregular).symm (Finsupp.single C 1))

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

namespace KltDP.Geometry

open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

/-- **The F03 intersection-number laws.** For a prime curve `C` on a normal projective surface over
`k` and Cartier divisors `D` on the surface: (1) `C·D = intersectionDegree C D` when `C ⊄ Supp D`;
(2) additivity in `D`; (3) dependence only on the Picard class of `O_X(D)`; (4) `C·D` is the value of
F02's `picardRestrictionDegreeHom` at `C` on the class of `O_X(D)`; (5) the `ℤ`-linear extension to the
Cartier class group recovers `C·D`. All universes coincide (`u`). -/
theorem f03_intersection_number_laws {k : Type u} [Field k] {X : NormalProjectiveSurface k}
    (C : X.PrimeCurve) :
    (∀ (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
        (hC : C.NotInSupport D hD), C.intersectionNumber D = (C.intersectionDegree D hD hC : ℤ)) ∧
    (∀ D₁ D₂ : CartierDivisor X.toScheme,
        C.intersectionNumber (D₁ + D₂) = C.intersectionNumber D₁ + C.intersectionNumber D₂) ∧
    (∀ D₁ D₂ : CartierDivisor X.toScheme,
        cartierPicardClass X.toScheme D₁ = cartierPicardClass X.toScheme D₂ →
          C.intersectionNumber D₁ = C.intersectionNumber D₂) ∧
    (∀ D : CartierDivisor X.toScheme,
        X.picardRestrictionDegreeHom C (cartierPicardHom X.toScheme D) = C.intersectionNumber D) ∧
    (∀ D : CartierDivisor X.toScheme,
        C.intersectionNumberClassHom (cartierClassMap X.toScheme D) = C.intersectionNumber D) :=
  ⟨fun D hD hC => C.intersectionNumber_eq_intersectionDegree D hD hC,
    fun D₁ D₂ => C.intersectionNumber_add D₁ D₂,
    fun D₁ D₂ h => C.intersectionNumber_eq_of_cartierPicardClass_eq D₁ D₂ h,
    fun D => C.picardRestrictionDegreeHom_cartierPicardHom D,
    fun D => C.intersectionNumberClassHom_classMap D⟩

/-- Universe check: the laws instantiate at a single universe `u`. -/
example {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    (D₁ D₂ : CartierDivisor X.toScheme) :
    C.intersectionNumber (D₁ + D₂) = C.intersectionNumber D₁ + C.intersectionNumber D₂ :=
  (f03_intersection_number_laws C).2.1 D₁ D₂

end KltDP.Geometry
