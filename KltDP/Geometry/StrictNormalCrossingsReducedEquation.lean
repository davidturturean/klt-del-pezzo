import KltDP.Geometry.StrictNormalCrossingsSurfaceEquation
import KltDP.Geometry.RegularLocalParameterIdealRadical
import KltDP.Geometry.RegularLocalDimensionTwo

/-!
# Original SNC equations generate radical ideals on surfaces

The full parameter system has the actual local dimension. Under the bound
two, a nonunit equation either generates the one-dimensional maximal ideal
or is a unit times one or both original surface parameters. Their radicality
is derived from those actual parameters. No radicality, domain, factoriality
or coordinate identification is an additional hypothesis.
-/

noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

namespace KltDP.Geometry

namespace IsStrictNormalCrossingsEquation

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The original one- or two-branch equation at a two-dimensional SNC
stalk generates a radical principal ideal. -/
theorem span_singleton_isRadical_of_dim_two {f : R}
    (hf : IsStrictNormalCrossingsEquation R f) (hdim : ringKrullDim R = 2) :
    (Ideal.span {f}).IsRadical := by
  rcases hf.surface_equation hdim with hu | ⟨a, b, v, hR, hspan, heq⟩
  · rw [Ideal.span_singleton_eq_top.mpr hu]
    exact le_top
  · rcases heq with heq | heq
    · rw [heq, Ideal.span_singleton_mul_left_unit v.isUnit]
      exact (RegularLocalTwoParameters.first_span_isPrime hR hdim a b hspan).isRadical
    · rw [heq, Ideal.span_singleton_mul_left_unit v.isUnit]
      exact RegularLocalTwoParameters.product_span_isRadical hR hdim a b hspan

/-- Every original SNC equation in local dimension at most two generates
a radical principal ideal. The nonunit SNC witness supplies regularity itself. -/
theorem span_singleton_isRadical_of_dim_le_two {f : R}
    (hf : IsStrictNormalCrossingsEquation R f) (hdim : ringKrullDim R ≤ 2) :
    (Ideal.span {f}).IsRadical := by
  by_cases htwo : ringKrullDim R = 2
  · exact hf.span_singleton_isRadical_of_dim_two htwo
  rcases hf with hu | ⟨d, t, ht, r, hr, hrd, v, hv⟩
  · rw [Ideal.span_singleton_eq_top.mpr hu]
    exact le_top
  · have hdcast : (d : WithBot ℕ∞) ≤ 2 := ht.2.1 ▸ hdim
    have hdle : d ≤ 2 := by exact_mod_cast hdcast
    have hdne : d ≠ 2 := by
      intro hd
      subst d
      exact htwo (by simpa using ht.2.1)
    have hd : d = 1 := by omega
    subst d
    have hrone : r = 1 := by omega
    subst r
    have htfun : t = ![t 0] := by
      funext i
      fin_cases i
      rfl
    have hspan : Ideal.span {t 0} = maximalIdeal R := by
      simpa only [Matrix.range_cons_empty] using
        (congrArg (fun s : Fin 1 → R => Ideal.span (Set.range s)) htfun).symm.trans ht.2.2
    have heq : f = (v : R) * t 0 := by
      simpa [Fin.prod_univ_one] using hv
    rw [heq, Ideal.span_singleton_mul_left_unit v.isUnit, hspan]
    exact (inferInstance : (maximalIdeal R).IsPrime).isRadical

end IsStrictNormalCrossingsEquation

/-- The dimension bound is derived for every original surface stalk;
no smoothness or new local algebra hypothesis is needed beyond the SNC germ. -/
theorem NormalProjectiveSurface.snc_equation_span_isRadical
    {k : Type u} [Field k] (X : NormalProjectiveSurface k) (x : X.toScheme)
    {f : X.toScheme.presheaf.stalk x}
    (hf : IsStrictNormalCrossingsEquation (X.toScheme.presheaf.stalk x) f) :
    (Ideal.span {f}).IsRadical :=
  hf.span_singleton_isRadical_of_dim_le_two
    ((ringKrullDim_stalk_le_topologicalKrullDim X.toScheme x).trans X.dimension_two.le)

end KltDP.Geometry

#check @KltDP.Geometry.IsStrictNormalCrossingsEquation.span_singleton_isRadical_of_dim_le_two
#check @KltDP.Geometry.NormalProjectiveSurface.snc_equation_span_isRadical
#print axioms KltDP.Geometry.IsStrictNormalCrossingsEquation.span_singleton_isRadical_of_dim_le_two
#print axioms KltDP.Geometry.NormalProjectiveSurface.snc_equation_span_isRadical
