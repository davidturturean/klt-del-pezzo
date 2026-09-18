import KltDP.Geometry.BirationalRationalPrincipalImage
import KltDP.Geometry.BirationalRationalWeilSupport
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The original rational class kernel is principal plus exceptional

This is an exact statement about original finite rational Weil sums.
The supported submodule is indexed by the actual contracted prime curves
of the original proper birational map. Principal divisors are lifted by
the original function-field map, so no divisor descent premise is needed.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.BirationalWeilPushforward

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

include hbir

/-- The original prime above a target curve is not contracted. -/
theorem abovePrimeCurve_not_exceptional (C : X.PrimeCurve) :
    ¬ IsExceptionalCurve π (abovePrimeCurve π hbir C) := by
  rintro ⟨x, hx⟩
  have hclosed : IsClosed ({x} : Set X.toScheme) :=
    hx ▸ π.isClosedMap _ (abovePrimeCurve π hbir C).isClosed
  have hpoint : π.base (abovePrimeCurve π hbir C).genericPoint = x := by
    have hmem := Set.mem_image_of_mem π.base (abovePrimeCurve π hbir C).genericPoint_mem
    rw [hx] at hmem
    exact hmem
  have heq : C.genericPoint = x :=
    (abovePrimeCurve_map_genericPoint π hbir C).symm.trans hpoint
  exact C.not_isClosed_singleton_genericPoint (heq.symm ▸ hclosed)

/-- The literal rational Weil pushforward kills exactly the divisors
supported on the actual contracted primes. -/
theorem rationalPushforward_ker :
    LinearMap.ker (rationalPushforward π hbir) =
      Finsupp.supported ℚ ℚ {C : S.PrimeCurve | IsExceptionalCurve π C} := by
  ext D
  constructor
  · intro hD
    exact support_subset_exceptional_of_rationalPushforward_eq_zero π hbir D hD
  · intro hD
    apply Finsupp.ext
    intro C
    change D (abovePrimeCurve π hbir C) = 0
    exact (Finsupp.mem_supported' ℚ D).mp hD _
      (abovePrimeCurve_not_exceptional π hbir C)

/-- Vanishing of the original target rational class is exactly a sum of
an original source principal class and an actual exceptional divisor. -/
theorem rationalClassPushforward_ker :
    LinearMap.ker (X.rationalWeilClassMap.comp (rationalPushforward π hbir)) =
      S.rationalPrincipalSubmodule ⊔
        Finsupp.supported ℚ ℚ {C : S.PrimeCurve | IsExceptionalCurve π C} := by
  rw [LinearMap.ker_comp]
  change (LinearMap.ker X.rationalPrincipalSubmodule.mkQ).comap (rationalPushforward π hbir) = _
  rw [Submodule.ker_mkQ, ← rationalPushforward_map_principalSubmodule π hbir,
    Submodule.comap_map_eq, rationalPushforward_ker π hbir]

/-- The same exact kernel, expressed using the original prime singleton
generators rather than a supplied exceptional basis. -/
theorem rationalClassPushforward_ker_eq_principal_sup_span :
    LinearMap.ker (X.rationalWeilClassMap.comp (rationalPushforward π hbir)) =
      S.rationalPrincipalSubmodule ⊔ Submodule.span ℚ
        ((fun C : S.PrimeCurve => Finsupp.single C (1 : ℚ)) ''
          {C : S.PrimeCurve | IsExceptionalCurve π C}) := by
  rw [rationalClassPushforward_ker π hbir, Finsupp.supported_eq_span_single]

end KltDP.Geometry.BirationalWeilPushforward

#check @KltDP.Geometry.BirationalWeilPushforward.rationalClassPushforward_ker_eq_principal_sup_span
#print axioms KltDP.Geometry.BirationalWeilPushforward.rationalClassPushforward_ker_eq_principal_sup_span
