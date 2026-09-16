import KltDP.Geometry.CartierPicardEndpointRational
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Rational linear equivalence and the integral Picard group

Rational principal divisors are the rational span of actual principal
divisors of nonzero rational functions. Rational linear equivalence is
equality modulo this subspace. Clearing denominators proves that a single
positive integral multiple of the difference is principal.

For integral divisors this is equivalent to torsion of the difference of
their original integral Weil classes. On a regular surface it is equivalent
to torsion of the corresponding original sheaf Picard classes. Thus the
integral Picard group is retained: rational linear equivalence kills its
torsion, and is not identified with equality of integral Picard classes.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The actual principal-divisor map followed by coefficient rationalization. -/
def rationalPrincipalDivisorHom :
    Additive X.toScheme.functionFieldˣ →+ X.RationalWeilDivisor :=
  (rationalizeWeilDivisor X).comp X.principalDivisorHom

/-- The rational span of the actual principal divisors. -/
def rationalPrincipalSubmodule : Submodule ℚ X.RationalWeilDivisor :=
  Submodule.span ℚ (Set.range X.rationalPrincipalDivisorHom)

/-- Rational linear equivalence uses the actual rational principal subspace. -/
def QLinearlyEquivalent (D E : X.RationalWeilDivisor) : Prop :=
  D - E ∈ X.rationalPrincipalSubmodule

/-- An arbitrary rational principal difference has one actual rational
function witness after a positive integer clears all denominators. -/
theorem qLinearlyEquivalent_iff_positive_principal_multiple
    (D E : X.RationalWeilDivisor) :
    X.QLinearlyEquivalent D E ↔
      ∃ n : ℕ, 0 < n ∧ ∃ f : X.toScheme.functionFieldˣ,
        n • (D - E) = rationalizeWeilDivisor X (X.principalDivisor f) := by
  change D - E ∈ Submodule.span ℚ (Set.range X.rationalPrincipalDivisorHom) ↔ _
  rw [mem_ratSpan_range_iff]
  constructor
  · rintro ⟨n, hn, f, hf⟩
    exact ⟨n, hn, f.toMul, hf.symm⟩
  · rintro ⟨n, hn, f, hf⟩
    exact ⟨n, hn, Additive.ofMul f, hf.symm⟩

/-- On integral divisors the equality is an equality of the original
integral coefficients, not merely an equality after rationalization. -/
theorem qLinearlyEquivalent_integral_iff
    (D E : X.WeilDivisor) :
    X.QLinearlyEquivalent (rationalizeWeilDivisor X D) (rationalizeWeilDivisor X E) ↔
      ∃ n : ℕ, 0 < n ∧ X.LinearlyEquivalent (n • D) (n • E) := by
  rw [X.qLinearlyEquivalent_iff_positive_principal_multiple]
  constructor
  · rintro ⟨n, hn, f, hf⟩
    refine ⟨n, hn, f, rationalizeWeilDivisor_injective ?_⟩
    simpa only [map_sub, map_nsmul, smul_sub] using hf
  · rintro ⟨n, hn, f, hf⟩
    refine ⟨n, hn, f, ?_⟩
    simpa only [map_sub, map_nsmul, smul_sub] using
      congrArg (rationalizeWeilDivisor X) hf

/-- Rational linear equivalence of integral divisors is exactly torsion
of their difference in the original integral Weil class group. -/
theorem qLinearlyEquivalent_integral_iff_torsion_weilClass
    (D E : X.WeilDivisor) :
    X.QLinearlyEquivalent (rationalizeWeilDivisor X D) (rationalizeWeilDivisor X E) ↔
      ∃ n : ℕ, 0 < n ∧ n • (X.weilClassMap D - X.weilClassMap E) = 0 := by
  rw [X.qLinearlyEquivalent_integral_iff]
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    have hclasses := (X.linearlyEquivalent_iff_weilClassMap_eq _ _).mp h
    simpa only [map_nsmul, nsmul_sub, sub_eq_zero] using hclasses
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, (X.linearlyEquivalent_iff_weilClassMap_eq _ _).mpr ?_⟩
    simpa only [map_nsmul, nsmul_sub, sub_eq_zero] using h

/-- The rational divisor class space uses the actual rational principal
subspace. It is not a numerical-equivalence quotient. -/
abbrev RationalWeilClassGroup := X.RationalWeilDivisor ⧸ X.rationalPrincipalSubmodule

/-- The canonical rational linear class map. -/
def rationalWeilClassMap : X.RationalWeilDivisor →ₗ[ℚ] X.RationalWeilClassGroup :=
  X.rationalPrincipalSubmodule.mkQ

/-- The quotient relation is precisely the previously defined rational
linear equivalence, including its original difference orientation. -/
theorem rationalWeilClassMap_eq_iff (D E : X.RationalWeilDivisor) :
    X.rationalWeilClassMap D = X.rationalWeilClassMap E ↔ X.QLinearlyEquivalent D E := by
  change Submodule.Quotient.mk D = Submodule.Quotient.mk E ↔ _
  exact Submodule.Quotient.eq X.rationalPrincipalSubmodule

/-- Ordinary linear equivalence implies rational linear equivalence. -/
theorem qLinearlyEquivalent_of_linearlyEquivalent {D E : X.WeilDivisor}
    (h : X.LinearlyEquivalent D E) :
    X.QLinearlyEquivalent (rationalizeWeilDivisor X D) (rationalizeWeilDivisor X E) :=
  (X.qLinearlyEquivalent_integral_iff D E).mpr ⟨1, Nat.zero_lt_one, by simpa using h⟩

/-- Actual principal divisors vanish in the rational class space. -/
theorem rationalWeilClassMap_principal (f : X.toScheme.functionFieldˣ) :
    X.rationalWeilClassMap (rationalizeWeilDivisor X (X.principalDivisor f)) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero X.rationalPrincipalSubmodule).mpr
  exact Submodule.subset_span ⟨Additive.ofMul f, rfl⟩

/-- The original integral divisor classes map into rational divisor classes
through the actual coefficient inclusion. -/
def weilClassRationalization : X.WeilClassGroup →+ X.RationalWeilClassGroup :=
  QuotientAddGroup.lift X.principalDivisors
    (X.rationalWeilClassMap.toAddMonoidHom.comp (rationalizeWeilDivisor X)) (by
      intro D hD
      obtain ⟨f, rfl⟩ := (X.mem_principalDivisors_iff D).mp hD
      exact X.rationalWeilClassMap_principal f)

/-- Rationalization on a representative is the original coefficient inclusion. -/
@[simp]
theorem weilClassRationalization_class (D : X.WeilDivisor) :
    X.weilClassRationalization (X.weilClassMap D) =
      X.rationalWeilClassMap (rationalizeWeilDivisor X D) := rfl

/-- The integral-to-rational class map kills exactly the torsion in the
original integral class group; it is not asserted to be injective. -/
theorem weilClassRationalization_eq_zero_iff (c : X.WeilClassGroup) :
    X.weilClassRationalization c = 0 ↔ ∃ n : ℕ, 0 < n ∧ n • c = 0 := by
  obtain ⟨D, rfl⟩ := X.weilClassMap_surjective c
  have h := X.qLinearlyEquivalent_integral_iff_torsion_weilClass D 0
  rw [← X.rationalWeilClassMap_eq_iff] at h
  simpa only [map_zero, sub_zero, weilClassRationalization_class] using h

section Regular

variable [IsAlgClosed k]
variable (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The actual integral sheaf Picard group maps to the rational Weil
class space using the proved regular-surface class equivalence. -/
def regularPicardRationalization : Additive X.toScheme.Pic →+ X.RationalWeilClassGroup :=
  X.weilClassRationalization.comp (X.regularWeilClassPicardEquiv hregular).symm.toAddMonoidHom

/-- The rational class of the original O(D) is the rational class of its
actual Cartier-to-Weil image. -/
theorem regularPicardRationalization_of_cartier (D : CartierDivisor X.toScheme) :
    X.regularPicardRationalization hregular (cartierPicardHom X.toScheme D) =
      X.rationalWeilClassMap (rationalizeWeilDivisor X (X.cartierToWeilHom D)) := by
  have hD : X.regularWeilClassPicardEquiv hregular
      (X.weilClassMap (X.cartierToWeilHom D)) = cartierPicardHom X.toScheme D :=
    congrArg Additive.ofMul (X.regularWeilClassPicardEquiv_of_cartier hregular D)
  rw [← hD]
  change X.weilClassRationalization
      ((X.regularWeilClassPicardEquiv hregular).symm
        ((X.regularWeilClassPicardEquiv hregular) _)) = _
  rw [AddEquiv.symm_apply_apply, X.weilClassRationalization_class]

/-- Passing from actual integral Picard classes to rational divisor classes
kills exactly torsion. The integral group has not been replaced by its
rational class space. -/
theorem regularPicardRationalization_eq_zero_iff (c : Additive X.toScheme.Pic) :
    X.regularPicardRationalization hregular c = 0 ↔
      ∃ n : ℕ, 0 < n ∧ n • c = 0 := by
  change X.weilClassRationalization
    ((X.regularWeilClassPicardEquiv hregular).symm c) = 0 ↔ _
  rw [X.weilClassRationalization_eq_zero_iff]
  constructor
  · rintro ⟨n, hn, hc⟩
    refine ⟨n, hn, ?_⟩
    simpa only [map_nsmul, AddEquiv.apply_symm_apply, map_zero] using
      congrArg (X.regularWeilClassPicardEquiv hregular) hc
  · rintro ⟨n, hn, hc⟩
    refine ⟨n, hn, ?_⟩
    simpa only [map_nsmul, map_zero] using
      congrArg (X.regularWeilClassPicardEquiv hregular).symm hc

end Regular

end KltDP.Geometry.NormalProjectiveSurface
