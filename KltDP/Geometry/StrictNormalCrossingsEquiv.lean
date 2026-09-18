import KltDP.Geometry.StrictNormalCrossings
import KltDP.Geometry.RegularLocalEquiv

/-!
# Transport strict normal crossings through the original local-ring isomorphism

The actual parameter family is mapped by the given ring isomorphism. Its
regularity, dimension, and maximal-ideal spanning property are transported
separately. The same original equation is then mapped, including its unit
and its distinct parameter factors. No new parameter family is assumed.
-/

noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

namespace KltDP.Geometry

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- Map the entire original regular parameter system along a ring isomorphism. -/
theorem IsRegularParameterFamily.map_equiv (e : R ≃+* S)
    {d : ℕ} {t : Fin d → R} (ht : IsRegularParameterFamily R d t) :
    IsRegularParameterFamily S d (fun i => e (t i)) := by
  refine ⟨regularLocal_of_ringEquiv e ht.1,
    (ringKrullDim_eq_of_ringEquiv e).symm.trans ht.2.1, ?_⟩
  have hspan := congrArg (Ideal.map (e : R →+* S)) ht.2.2
  rw [Ideal.map_span] at hspan
  calc
    Ideal.span (Set.range (fun i => e (t i))) = Ideal.span (e '' Set.range t) :=
      congrArg Ideal.span (Set.range_comp' e t)
    _ = Ideal.map (e : R →+* S) (maximalIdeal R) := hspan
    _ = maximalIdeal S := IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)

/-- Map the original SNC equation and its explicit unit and parameter factors. -/
theorem IsStrictNormalCrossingsEquation.map_equiv (e : R ≃+* S)
    {f : R} (hf : IsStrictNormalCrossingsEquation R f) :
    IsStrictNormalCrossingsEquation S (e f) := by
  rcases hf with hf | ⟨d, t, ht, r, hr, hrd, v, hv⟩
  · exact Or.inl (hf.map (e : R →+* S))
  · refine Or.inr ⟨d, (fun i => e (t i)), ht.map_equiv e,
      r, hr, hrd, Units.map e.toMonoidHom v, ?_⟩
    simpa only [map_mul, map_prod, Units.coe_map] using congrArg e hv

/-- The actual local-ring isomorphism preserves and reflects SNC equations. -/
theorem isStrictNormalCrossingsEquation_iff_of_ringEquiv (e : R ≃+* S) (f : R) :
    IsStrictNormalCrossingsEquation R f ↔ IsStrictNormalCrossingsEquation S (e f) := by
  constructor
  · exact IsStrictNormalCrossingsEquation.map_equiv e
  · intro hf
    simpa only [e.symm_apply_apply] using hf.map_equiv e.symm

end KltDP.Geometry

#check @KltDP.Geometry.IsStrictNormalCrossingsEquation.map_equiv
#print axioms KltDP.Geometry.IsStrictNormalCrossingsEquation.map_equiv
