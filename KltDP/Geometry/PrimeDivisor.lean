import KltDP.Geometry.Surface
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.AlgebraicGeometry.IdealSheaf
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Actual prime curves and finitely supported surface divisors

A prime curve is an actual nonempty irreducible closed subset of the given
surface with its subspace Krull dimension proved to be one. Integral and
rational divisors are the existing `Finsupp` types on these curves. Thus
their coefficients have finite support, while their geometric support is
the union of the specified closed curves and need not be a finite set.

The pinned Mathlib has no general scheme Weil-divisor or algebraic-cycle
type. This module reuses `IrreducibleCloseds`, `Finsupp`, their free-module
bases, and the existing vanishing ideal sheaf of a closed subset. Each
curve's ideal sheaf is radical and has exactly the stated carrier as support.

Here `PrimeDivisor` names the dimension-one curve indexing type on the
actual surface. The dimension-one/codimension-one comparison is a separate
adapter, not a definitional identification made by this file. Constructing
the corresponding reduced closed immersion and proving its scheme properties
also remain separate. No intersection, adjunction, Cartier, principal-divisor,
Picard, or numerical-class construction is claimed. This supplies a bounded
foundation for F02 and F03, not their completed statements.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace
open scoped BigOperators

universe u v w

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k]

/-- An actual irreducible closed curve, with dimension measured in its
subspace topology. No intersection or divisor-class data is stored. -/
def PrimeCurve (X : NormalProjectiveSurface k) :=
  { Z : IrreducibleCloseds X.toScheme // topologicalKrullDim (Z : Set X.toScheme) = 1 }

/-- The prime generators for surface divisors in this module. The separate
comparison with codimension-one points is not asserted by this abbreviation. -/
abbrev PrimeDivisor (X : NormalProjectiveSurface k) := X.PrimeCurve

namespace PrimeCurve

variable {X : NormalProjectiveSurface k}

instance : SetLike X.PrimeCurve X.toScheme where
  coe C := (C.1 : Set X.toScheme)
  coe_injective' _ _ h := Subtype.ext (IrreducibleCloseds.ext h)

@[ext]
theorem ext {C D : X.PrimeCurve} (h : (C : Set X.toScheme) = D) : C = D :=
  SetLike.coe_injective h

theorem isClosed (C : X.PrimeCurve) : IsClosed (C : Set X.toScheme) := C.1.isClosed

theorem isIrreducible (C : X.PrimeCurve) : IsIrreducible (C : Set X.toScheme) :=
  C.1.isIrreducible

theorem nonempty (C : X.PrimeCurve) : (C : Set X.toScheme).Nonempty :=
  C.isIrreducible.nonempty

theorem dimension_one (C : X.PrimeCurve) :
    topologicalKrullDim (C : Set X.toScheme) = 1 := C.2

/-- The same underlying curve viewed as an actual closed subset. -/
def closedSubset (C : X.PrimeCurve) : Closeds X.toScheme := ⟨C, C.isClosed⟩

@[simp]
theorem coe_closedSubset (C : X.PrimeCurve) :
    (C.closedSubset : Set X.toScheme) = C := rfl

/-- The actual generic scheme point of this irreducible closed curve. -/
def genericPoint (C : X.PrimeCurve) : X.Point := C.isIrreducible.genericPoint

theorem closure_genericPoint (C : X.PrimeCurve) :
    closure ({C.genericPoint} : Set X.toScheme) = C :=
  C.isIrreducible.closure_genericPoint C.isClosed

theorem genericPoint_mem (C : X.PrimeCurve) : C.genericPoint ∈ C :=
  (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem

/-- The canonical vanishing ideal sheaf on the original surface. This is
actual ideal-sheaf data, not an assumed reduced closed immersion. -/
def vanishingIdeal (C : X.PrimeCurve) : X.toScheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal C.closedSubset

@[simp]
theorem vanishingIdeal_support (C : X.PrimeCurve) :
    (C.vanishingIdeal.support : Set X.toScheme) = C := rfl

/-- The ideal data is radical, as required for the reduced induced
structure whose closed-immersion construction is a later adapter. -/
theorem vanishingIdeal_radical (C : X.PrimeCurve) :
    C.vanishingIdeal.radical = C.vanishingIdeal :=
  (Scheme.IdealSheafData.vanishingIdeal_support (I := C.vanishingIdeal)).symm

end PrimeCurve

/-- Actual integral divisors: finite integer sums of the stated prime curves. -/
abbrev WeilDivisor (X : NormalProjectiveSurface k) := X.PrimeDivisor →₀ ℤ

/-- Actual rational divisors, retaining every prime coefficient. This is
not a Picard-group tensor product or a numerical-equivalence quotient. -/
abbrev RationalWeilDivisor (X : NormalProjectiveSurface k) := X.PrimeDivisor →₀ ℚ

/-- The free abelian group presentation is the existing Mathlib equivalence. -/
def weilDivisorFreeAbelianEquiv (X : NormalProjectiveSurface k) :
    FreeAbelianGroup X.PrimeDivisor ≃+ X.WeilDivisor :=
  FreeAbelianGroup.equivFinsupp X.PrimeDivisor

/-- Prime curves form an actual integral basis of the divisor group. This
does not assert that this generally infinite basis is finite. -/
def weilDivisorBasis (X : NormalProjectiveSurface k) :
    Basis X.PrimeDivisor ℤ X.WeilDivisor := Finsupp.basisSingleOne

/-- The same prime curves form the rational divisor-space basis. -/
def rationalWeilDivisorBasis (X : NormalProjectiveSurface k) :
    Basis X.PrimeDivisor ℚ X.RationalWeilDivisor := Finsupp.basisSingleOne

section FiniteSupport

variable {X : NormalProjectiveSurface k} {A : Type v} [Zero A]

/-- The geometric support is a finite union of actual closed curves.
It is distinct from the finite set `D.support` of prime components. -/
def divisorSupport (D : X.PrimeDivisor →₀ A) : Set X.toScheme :=
  ⋃ C ∈ D.support, (C : Set X.toScheme)

/-- The component set is finite without an effectivity assumption. This
does not claim that the geometric support has finitely many points. -/
theorem divisor_componentSupport_finite (D : X.PrimeDivisor →₀ A) :
    (D.support : Set X.PrimeDivisor).Finite := D.support.finite_toSet

theorem mem_divisorSupport (D : X.PrimeDivisor →₀ A) (x : X.Point) :
    x ∈ divisorSupport D ↔ ∃ C : X.PrimeDivisor, D C ≠ 0 ∧ x ∈ C := by
  simp only [divisorSupport, Set.mem_iUnion, Finsupp.mem_support_iff, exists_prop]
  rfl

theorem divisorSupport_isClosed (D : X.PrimeDivisor →₀ A) :
    IsClosed (divisorSupport D) :=
  isClosed_biUnion_finset (fun C _ => C.isClosed)

@[simp]
theorem divisorSupport_zero : divisorSupport (0 : X.PrimeDivisor →₀ A) = ∅ := by
  simp [divisorSupport]

theorem primeCurve_subset_divisorSupport (D : X.PrimeDivisor →₀ A)
    {C : X.PrimeDivisor} (hC : D C ≠ 0) :
    (C : Set X.toScheme) ⊆ divisorSupport D := by
  intro x hx
  exact (mem_divisorSupport D x).mpr ⟨C, hC, hx⟩

end FiniteSupport

section FiniteSums

variable {X : NormalProjectiveSurface k} {A : Type v} [AddCommMonoid A]

/-- Every divisor is the finite sum of its actual prime coefficients. -/
theorem divisor_sum_single (D : X.PrimeDivisor →₀ A) :
    (∑ C ∈ D.support, Finsupp.single C (D C)) = D :=
  Finsupp.sum_single D

/-- Coefficients of a finite divisor sum are the sums of the coefficients;
repeated prime labels are combined in the existing Finsupp group. -/
theorem divisor_finset_sum_apply {ι : Type w} (s : Finset ι)
    (D : ι → X.PrimeDivisor →₀ A) (C : X.PrimeDivisor) :
    (∑ i ∈ s, D i) C = ∑ i ∈ s, D i C :=
  Finsupp.finset_sum_apply s D C

end FiniteSums

section LinearExtension

variable {X : NormalProjectiveSurface k} {R : Type v} [Semiring R]
variable {V : Type w} [AddCommMonoid V] [Module R V]

/-- Extend values on actual prime curves by finite linear combination.
Future intersection constructions must supply and justify those values. -/
def divisorLinearExtension (f : X.PrimeDivisor → V) :
    (X.PrimeDivisor →₀ R) →ₗ[R] V := Finsupp.linearCombination R f

theorem divisorLinearExtension_apply (f : X.PrimeDivisor → V)
    (D : X.PrimeDivisor →₀ R) :
    divisorLinearExtension f D = ∑ C ∈ D.support, D C • f C := rfl

@[simp]
theorem divisorLinearExtension_single (f : X.PrimeDivisor → V)
    (C : X.PrimeDivisor) (a : R) :
    divisorLinearExtension f (Finsupp.single C a) = a • f C :=
  Finsupp.linearCombination_single _ _ _

end LinearExtension

section EffectivityAndRationalization

variable {X : NormalProjectiveSurface k}

/-- Effectivity refers to every actual prime coefficient. -/
def EffectiveDivisor {A : Type v} [Zero A] [LE A] (D : X.PrimeDivisor →₀ A) : Prop :=
  ∀ C, 0 ≤ D C

/-- The integral-to-rational map changes coefficients by the canonical
integer cast and retains the same actual prime curves. -/
def rationalizeWeilDivisor (X : NormalProjectiveSurface k) :
    X.WeilDivisor →+ X.RationalWeilDivisor :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ)

@[simp]
theorem rationalizeWeilDivisor_apply (D : X.WeilDivisor) (C : X.PrimeDivisor) :
    rationalizeWeilDivisor X D C = (D C : ℚ) := rfl

theorem rationalizeWeilDivisor_injective : Function.Injective (rationalizeWeilDivisor X) :=
  Finsupp.mapRange_injective (Int.castAddHom ℚ)
    (map_zero (Int.castAddHom ℚ)) Int.cast_injective

@[simp]
theorem rationalizeWeilDivisor_single (C : X.PrimeDivisor) (a : ℤ) :
    rationalizeWeilDivisor X (Finsupp.single C a) = Finsupp.single C (a : ℚ) :=
  Finsupp.mapRange_single (hf := map_zero (Int.castAddHom ℚ))

/-- Rationalization preserves the exact finite set of prime components. -/
@[simp]
theorem rationalizeWeilDivisor_componentSupport (D : X.WeilDivisor) :
    (rationalizeWeilDivisor X D).support = D.support :=
  Finsupp.support_mapRange_of_injective (map_zero (Int.castAddHom ℚ)) D Int.cast_injective

/-- The geometric support is also preserved by the coefficient inclusion. -/
@[simp]
theorem divisorSupport_rationalizeWeilDivisor (D : X.WeilDivisor) :
    divisorSupport (rationalizeWeilDivisor X D) = divisorSupport D := by
  simp only [divisorSupport, rationalizeWeilDivisor_componentSupport]

@[simp]
theorem effective_rationalizeWeilDivisor_iff (D : X.WeilDivisor) :
    EffectiveDivisor (rationalizeWeilDivisor X D) ↔ EffectiveDivisor D := by
  simp only [EffectiveDivisor, rationalizeWeilDivisor_apply, Int.cast_nonneg]

end EffectivityAndRationalization

end KltDP.Geometry.NormalProjectiveSurface
