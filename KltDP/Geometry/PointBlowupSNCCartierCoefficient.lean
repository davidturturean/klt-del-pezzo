import KltDP.Geometry.PointBlowupSNCOriginalParameters
import KltDP.Geometry.PointBlowupOriginalParameterChartCover
import KltDP.Geometry.PointBlowupCenterStalkCoefficients
import KltDP.Geometry.PointBlowupCartierCrossingCoefficient
import KltDP.Geometry.FiniteTypeNoetherian

/-!
# Exceptional coefficients from the actual original SNC Cartier divisor

The original SNC equation supplies its own original numerator pair.
Original chart coverage and the original centre-stalk coefficient square
are proved inputs. Thus no parameter choice, coordinate alignment, chart
coverage or pulled multiplicity is assumed in the final coefficient theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

private theorem unit_mul_equation_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (t f : A) (v : Bˣ) (h : e t = (v : B) * e f) :
    t = (Units.map e.symm.toMonoidHom v : Aˣ) * f := by
  apply e.injective
  change e t = e (e.symm (v : B) * f)
  rw [map_mul, e.apply_symm_apply]
  exact h

namespace PointBlowupExceptionalPrimeStalk

open AffineBlowup PointBlowupGluing PointBlowupChartStalk

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (hcenter : (projection j q hclosed).base C.genericPoint = j.base q)

local instance : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian

private theorem coefficient_cases_on_original_chart
    (a b : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a))
    (hC : (chartInclusion j q hclosed a).base P = C.genericPoint)
    (ha : (centerParameter q a : Localization.AtPrime q.asIdeal) ∈
      nonZeroDivisors (Localization.AtPrime q.asIdeal))
    (hb : Ideal.Quotient.mk
      (Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)})
      (centerParameter q b : Localization.AtPrime q.asIdeal) ∈ nonZeroDivisors
        (Localization.AtPrime q.asIdeal ⧸
          Ideal.span {(centerParameter q a : Localization.AtPrime q.asIdeal)}))
    (hI : centerIdeal q = Ideal.span
      {(centerParameter q a : Localization.AtPrime q.asIdeal),
        (centerParameter q b : Localization.AtPrime q.asIdeal)})
    (D : CartierDivisor X.toScheme) (c : RegularCartierEquationChart X.toScheme D)
    (hx : (projection j q hclosed).base C.genericPoint ∈ c.chart.openSet)
    (hform : let e := centerStalkEquiv X j q hclosed C hcenter
      let t := X.toScheme.presheaf.germ c.chart.openSet
        ((projection j q hclosed).base C.genericPoint) hx c.coefficient
      IsUnit (e t) ∨ ∃ v : (Localization.AtPrime q.asIdeal)ˣ,
        e t = (v : Localization.AtPrime q.asIdeal) *
          algebraMap R (Localization.AtPrime q.asIdeal) (a : R) ∨
        e t = (v : Localization.AtPrime q.asIdeal) *
          algebraMap R (Localization.AtPrime q.asIdeal) (b : R) ∨
        e t = (v : Localization.AtPrime q.asIdeal) *
          (algebraMap R (Localization.AtPrime q.asIdeal) (a : R) *
            algebraMap R (Localization.AtPrime q.asIdeal) (b : R))) :
    let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
    letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
    (sourceSurface X j q hclosed).cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C = 0 ∨
      (sourceSurface X j q hclosed).cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C = 1 ∨
      (sourceSurface X j q hclosed).cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C = 2 := by
  let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
  letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
  let e := centerStalkEquiv X j q hclosed C hcenter
  let t := X.toScheme.presheaf.germ c.chart.openSet
    ((projection j q hclosed).base C.genericPoint) hx c.coefficient
  let ga := baseCoefficientGerm X j q hclosed C a P hC (a : R)
  let gb := baseCoefficientGerm X j q hclosed C a P hC (b : R)
  have hga : e ga = algebraMap R (Localization.AtPrime q.asIdeal) (a : R) :=
    centerStalkEquiv_baseCoefficient X j q hclosed C hcenter a P hC (a : R)
  have hgb : e gb = algebraMap R (Localization.AtPrime q.asIdeal) (b : R) :=
    centerStalkEquiv_baseCoefficient X j q hclosed C hcenter a P hC (b : R)
  rcases hform with hu | ⟨v, hva | hvb | hvab⟩
  · have hu' : IsUnit (e t) := hu
    have hut : IsUnit t := by
      have hh := hu'.map e.symm.toMonoidHom
      change IsUnit (e.symm (e t)) at hh
      exact (e.symm_apply_apply t) ▸ hh
    exact Or.inl (DominantCartierPullback.coefficient_eq_zero_of_isUnit_germ π D c C hx hut)
  · have ht := unit_mul_equation_of_ringEquiv e t ga v
      (hva.trans (congrArg (fun z => (v : Localization.AtPrime q.asIdeal) * z) hga.symm))
    exact Or.inr (Or.inl (cartier_pullback_coefficient_of_branch
      X j q hclosed C a b P hC hcenter ha hb hI D c hx a (Or.inl rfl)
      (Units.map e.symm.toMonoidHom v) ht))
  · have ht := unit_mul_equation_of_ringEquiv e t gb v
      (hvb.trans (congrArg (fun z => (v : Localization.AtPrime q.asIdeal) * z) hgb.symm))
    exact Or.inr (Or.inl (cartier_pullback_coefficient_of_branch
      X j q hclosed C a b P hC hcenter ha hb hI D c hx b (Or.inr rfl)
      (Units.map e.symm.toMonoidHom v) ht))
  · have hprod : e (ga * gb) =
        algebraMap R (Localization.AtPrime q.asIdeal) (a : R) *
          algebraMap R (Localization.AtPrime q.asIdeal) (b : R) :=
      (map_mul e ga gb).trans (congrArg₂ (fun x y : Localization.AtPrime q.asIdeal => x * y) hga hgb)
    have ht := unit_mul_equation_of_ringEquiv e t (ga * gb) v
      (hvab.trans (congrArg (fun z => (v : Localization.AtPrime q.asIdeal) * z) hprod.symm))
    exact Or.inr (Or.inr (cartier_pullback_coefficient_of_crossing
      X j q hclosed C a b P hC hcenter ha hb hI D c hx
      (Units.map e.symm.toMonoidHom v) ht))

include hcenter in
/-- An actual original SNC Cartier divisor has exceptional coefficient
zero, one or two under the original point blowup. The arbitrary SNC germ
produces all parameters, numerator charts and coefficient comparisons. -/
theorem cartier_pullback_coefficient_zero_one_two_of_snc
    (D : CartierDivisor X.toScheme) (hD : IsStrictNormalCrossingsCartier X.toScheme D) :
    let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
    letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
    (sourceSurface X j q hclosed).cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C = 0 ∨
      (sourceSurface X j q hclosed).cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C = 1 ∨
      (sourceSurface X j q hclosed).cartierToWeilHom (DominantCartierPullback.pullbackHom π D) C = 2 := by
  obtain ⟨c, hx⟩ := hD.1 ((projection j q hclosed).base C.genericPoint)
  let e := centerStalkEquiv X j q hclosed C hcenter
  let t := X.toScheme.presheaf.germ c.chart.openSet
    ((projection j q hclosed).base C.genericPoint) hx c.coefficient
  have hsnc : IsStrictNormalCrossingsEquation (Localization.AtPrime q.asIdeal) (e t) :=
    (hD.2 c ((projection j q hclosed).base C.genericPoint) hx).map_equiv e
  obtain ⟨a, b, hspan, ha, hb, hform⟩ :=
    X.pointBlowup_snc_original_parameters j q hclosed (e t) hsnc
  obtain ⟨d, hd, P, hC⟩ := exists_original_parameter_chart_at_center j q hclosed
    a b hspan C.genericPoint hcenter
  rcases hd with hda | hdb
  · subst d
    apply coefficient_cases_on_original_chart X j q hclosed C hcenter
      a b P hC ha hb hspan.symm D c hx
    rcases hform with hu | ⟨v, hv | hv⟩
    · exact Or.inl hu
    · exact Or.inr ⟨v, Or.inl hv⟩
    · exact Or.inr ⟨v, Or.inr (Or.inr hv)⟩
  · subst d
    have hspan' : Ideal.span {algebraMap R (Localization.AtPrime q.asIdeal) (b : R),
        algebraMap R (Localization.AtPrime q.asIdeal) (a : R)} = centerIdeal q :=
      Ideal.span_pair_comm.trans hspan
    let e0 := openImmersionStalkLocalizationEquiv j q
    have hR : RegularLocal (Localization.AtPrime q.asIdeal) :=
      regularLocal_of_ringEquiv e0 (X.regularPoints_of_isSmooth (j.base q))
    have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 2 :=
      (ringKrullDim_eq_of_ringEquiv e0).symm.trans
        (X.closed_stalk_dimension_two (j.base q) hclosed)
    have hmax : centerIdeal q = IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) :=
      Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)
    have hpair := RegularLocalTwoParameters.regular_pair hR hdim _ _ (hspan'.trans hmax)
    apply coefficient_cases_on_original_chart X j q hclosed C hcenter
      b a P hC hpair.1 hpair.2 hspan'.symm D c hx
    rcases hform with hu | ⟨v, hv | hv⟩
    · exact Or.inl hu
    · exact Or.inr ⟨v, Or.inr (Or.inl hv)⟩
    · refine Or.inr ⟨v, Or.inr (Or.inr ?_)⟩
      exact hv.trans (congrArg (fun z => (v : Localization.AtPrime q.asIdeal) * z) (mul_comm _ _))

end PointBlowupExceptionalPrimeStalk
end KltDP.Geometry
