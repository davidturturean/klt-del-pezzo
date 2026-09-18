import KltDP.Geometry.FinitePrimeCartierSumCoefficients

/-!
# The original support of a finite reduced prime Cartier sum

The actual Weil coefficient calculation supplies regular equations and
identifies the support of the actual divisor ideal with precisely the
union of the original prime-curve carriers. This identifies the object
used by the finite SNC construction, without a support equality premise.
-/

noncomputable section

open AlgebraicGeometry

universe u v

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  {I : Type v} [Fintype I] (C : I → X.PrimeCurve) (hinj : Function.Injective C)

include hinj in
/-- The original finite prime sum has actual regular equation charts. -/
theorem finite_primeCartier_sum_hasRegularEquations :
    HasRegularCartierEquations X.toScheme (∑ i, X.primeCurveCartier hregular (C i)) := by
  letI := X.stalks_uniqueFactorizationMonoid_of_regular hregular
  exact X.hasRegularCartierEquations_of_effective_weil _
    (X.finite_primeCartier_sum_effective hregular C hinj)

/-- The actual Cartier divisor ideal is supported on precisely the union
of the original prime curves in the family. -/
theorem finite_primeCartier_sum_support :
    ((effectiveCartierIdealDataOfRegularEquations X.toScheme
      (∑ i, X.primeCurveCartier hregular (C i))
      (X.finite_primeCartier_sum_hasRegularEquations hregular C hinj)).support :
        Set X.toScheme) = ⋃ i, (C i : Set X.toScheme) := by
  classical
  letI := X.stalks_uniqueFactorizationMonoid_of_regular hregular
  ext x
  obtain ⟨c, hxc⟩ := X.finite_primeCartier_sum_hasRegularEquations hregular C hinj x
  simp only [SetLike.mem_coe]
  rw [PrimeCurve.mem_support_iff_not_isUnit_germ _
      (X.finite_primeCartier_sum_hasRegularEquations hregular C hinj) c x hxc,
    X.regularCartierEquation_germ_isUnit_iff _ c ⟨x, hxc⟩]
  constructor
  · intro hn
    by_contra hx
    apply hn
    intro E hxE
    rw [X.finite_primeCartier_sum_coefficient hregular C hinj E]
    apply if_neg
    rintro ⟨i, rfl⟩
    exact hx (Set.mem_iUnion.mpr ⟨i, hxE⟩)
  · intro hx hz
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have h := hz (C i) hxi
    rw [X.finite_primeCartier_sum_coefficient hregular C hinj (C i),
      if_pos (Set.mem_range_self i)] at h
    exact one_ne_zero h

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.finite_primeCartier_sum_support
