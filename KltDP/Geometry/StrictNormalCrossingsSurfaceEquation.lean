import KltDP.Geometry.StrictNormalCrossings

/-!
# The actual equation alternatives at a two-dimensional SNC stalk

The original SNC parameter system has the actual Krull dimension, so at
a two-dimensional stalk it has two parameters. Its distinct factors give
exactly the unit, one-branch, or two-branch equation. The parameters below
are extracted from the given SNC equation, not arbitrary etale coordinates.
-/

noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

namespace KltDP.Geometry

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Explicit equation alternatives for the original SNC germ in dimension two. -/
theorem IsStrictNormalCrossingsEquation.surface_equation
    {f : R} (hf : IsStrictNormalCrossingsEquation R f)
    (hdim : ringKrullDim R = 2) :
    IsUnit f ∨ ∃ (a b : R) (v : Rˣ),
      RegularLocal R ∧ Ideal.span {a, b} = maximalIdeal R ∧
      (f = (v : R) * a ∨ f = (v : R) * (a * b)) := by
  rcases hf with hf | ⟨d, t, ht, r, hr, hrd, v, hv⟩
  · exact Or.inl hf
  · have hd : d = 2 := by
      exact_mod_cast ht.2.1.symm.trans hdim
    subst d
    have htfun : t = ![t 0, t 1] := by
      funext i
      fin_cases i <;> rfl
    have hspan : Ideal.span {t 0, t 1} = maximalIdeal R := by
      simpa only [Matrix.range_cons_cons_empty] using
        (congrArg (fun s : Fin 2 → R => Ideal.span (Set.range s)) htfun).symm.trans ht.2.2
    refine Or.inr ⟨t 0, t 1, v, ht.1, hspan, ?_⟩
    have hr_cases : r = 1 ∨ r = 2 := by omega
    rcases hr_cases with rfl | rfl
    · exact Or.inl (by simpa [Fin.prod_univ_one] using hv)
    · exact Or.inr (by simpa [Fin.prod_univ_two] using hv)

end KltDP.Geometry

#check @KltDP.Geometry.IsStrictNormalCrossingsEquation.surface_equation
#print axioms KltDP.Geometry.IsStrictNormalCrossingsEquation.surface_equation
