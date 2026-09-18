import KltDP.Geometry.RegularLocalParameterQuotient
import KltDP.Geometry.RegularLocalDimensionTwo

/-!
# The actual cotangent bound for a principal local quotient

The accepted cotangent kernel theorem identifies the kernel with the line
spanned by the original equation's cotangent class, including when that
class is zero. Rank-nullity therefore bounds the original ambient
cotangent dimension by the quotient dimension plus one. At an actual
two-dimensional local domain, quotient cotangent dimension at most one
then proves ambient regularity.

This algebraic adapter uses the actual local map and its principal kernel.
It does not assume the equation has nonzero cotangent class or that the
ambient ring is regular. Geometric applications must derive the quotient
bound and identify the original stalk-map kernel.
-/

noncomputable section
open IsLocalRing
universe u

namespace KltDP.Geometry.RegularLocalParameterQuotient

variable {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]

/-- A principal kernel increases the original cotangent dimension by at most one. -/
theorem cotangent_finrank_le_quotient_add_one
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f)
    {x : R} (hx : x ∈ maximalIdeal R)
    (hker : RingHom.ker f = Ideal.span {x}) :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤
      Module.finrank (ResidueField S) (CotangentSpace S) + 1 := by
  have hdim : Module.finrank (ResidueField R)
      (LinearMap.ker (cotangentSemilinearMap f)) ≤ 1 := by
    rw [cotangent_ker_eq_span_parameter f hf hx hker]
    by_cases hzero : (maximalIdeal R).toCotangent ⟨x, hx⟩ = 0
    · rw [hzero, Submodule.span_zero_singleton, finrank_bot]
      exact Nat.zero_le 1
    · exact (finrank_span_singleton hzero).le
  have heq := Submodule.finrank_quotient_add_finrank
    (LinearMap.ker (cotangentSemilinearMap f))
  rw [cotangent_quotient_finrank_eq f hf] at heq
  omega

/-- A two-dimensional local domain is regular when an actual principal quotient has
cotangent dimension at most one. All regularity of the ambient ring is derived. -/
theorem regularLocal_of_principal_quotient_cotangent_le_one [IsDomain R]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f)
    {x : R} (hx : x ∈ maximalIdeal R)
    (hker : RingHom.ker f = Ideal.span {x}) (hdim : ringKrullDim R = 2)
    (hquot : Module.finrank (ResidueField S) (CotangentSpace S) ≤ 1) :
    RegularLocal R := by
  have hrank : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 2 :=
    (cotangent_finrank_le_quotient_add_one f hf hx hker).trans (Nat.add_le_add_right hquot 1)
  refine ⟨inferInstance, le_antisymm
    (ringKrullDim_le_finrank_cotangentSpace_of_le_two R hdim.le) ?_⟩
  rw [hdim]
  exact_mod_cast hrank

end KltDP.Geometry.RegularLocalParameterQuotient

#print axioms KltDP.Geometry.RegularLocalParameterQuotient.cotangent_finrank_le_quotient_add_one
#print axioms KltDP.Geometry.RegularLocalParameterQuotient.regularLocal_of_principal_quotient_cotangent_le_one
