import KltDP.Geometry.CotangentGenerators
import KltDP.Geometry.RationalTreePicardComponentLeaf
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Tactic.FinCases

/-!
# The reduced intersection from actual transverse branch germs

Two elements of the original branch ideals whose classes are independent
in a two-dimensional actual cotangent space generate the maximal ideal,
by the existing Nakayama theorem. Singleton support then upgrades this
local equality to equality of the original affine sum ideal with the
original point ideal. Reducedness of its quotient is a conclusion.

The final statement uses the actual component-point tree to produce the
leaf and its singleton support. Its remaining inputs are the actual branch
germs and their first-order transversality in the original scheme stalk.
Deriving those inputs from the manuscript's intrinsic nodal hypotheses remains required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u v

namespace KltDP.Geometry.RationalTreePicard

private theorem local_sup_eq_maximal_of_cotangent_independent
    (R : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hI : I ≤ maximalIdeal R) (hJ : J ≤ maximalIdeal R)
    (w : Fin 2 → maximalIdeal R) (hw0 : (w 0 : R) ∈ I) (hw1 : (w 1 : R) ∈ J)
    (hdim : Module.finrank (ResidueField R) (CotangentSpace R) = 2)
    (hind : LinearIndependent (ResidueField R)
      (fun i => (maximalIdeal R).toCotangent (w i))) :
    I ⊔ J = maximalIdeal R := by
  have hspan : Ideal.span (Set.range (fun i => (w i : R))) = maximalIdeal R :=
    (maximal_generators_iff_cotangent_spans w).mpr
      (hind.span_eq_top_of_card_eq_finrank (by
        simpa only [Fintype.card_fin] using hdim.symm))
  apply le_antisymm (sup_le hI hJ)
  rw [← hspan]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact (le_sup_left : I ≤ I ⊔ J) hw0
  · exact (le_sup_right : J ≤ I ⊔ J) hw1

/-- First-order transversality in an actual localization, together with
the actual singleton support, identifies the original intersection ideal.
Neither ideal generation nor quotient reducedness is an input. -/
theorem nodeIdeal_eq_of_transverse_localization
    (A : Type u) [CommRing A] (I J : Ideal A) (q : PrimeSpectrum A)
    (hsupport : PrimeSpectrum.zeroLocus (I ⊔ J : Ideal A) = {q})
    (R : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra A R] [IsLocalization.AtPrime R q.asIdeal]
    (w : Fin 2 → maximalIdeal R)
    (hw0 : (w 0 : R) ∈ I.map (algebraMap A R))
    (hw1 : (w 1 : R) ∈ J.map (algebraMap A R))
    (hdim : Module.finrank (ResidueField R) (CotangentSpace R) = 2)
    (hind : LinearIndependent (ResidueField R)
      (fun i => (maximalIdeal R).toCotangent (w i))) :
    I ⊔ J = q.asIdeal := by
  have hle : I ⊔ J ≤ q.asIdeal := by
    apply (PrimeSpectrum.mem_zeroLocus q (I ⊔ J : Ideal A)).mp
    rw [hsupport]
    exact Set.mem_singleton q
  have hI : I.map (algebraMap A R) ≤ maximalIdeal R := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [IsLocalization.AtPrime.comap_maximalIdeal R q.asIdeal]
    exact le_sup_left.trans hle
  have hJ : J.map (algebraMap A R) ≤ maximalIdeal R := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [IsLocalization.AtPrime.comap_maximalIdeal R q.asIdeal]
    exact le_sup_right.trans hle
  have hlocal : (I ⊔ J).map (algebraMap A R) = maximalIdeal R := by
    rw [Ideal.map_sup]
    exact local_sup_eq_maximal_of_cotangent_independent R _ _ hI hJ w hw0 hw1 hdim hind
  apply le_antisymm hle
  apply Ideal.le_of_localization_maximal
  intro P hP
  letI : P.IsMaximal := hP
  by_cases hKP : I ⊔ J ≤ P
  · have hPmem : (⟨P, hP.isPrime⟩ : PrimeSpectrum A) ∈
        PrimeSpectrum.zeroLocus (I ⊔ J : Ideal A) :=
      (PrimeSpectrum.mem_zeroLocus _ _).mpr hKP
    rw [hsupport] at hPmem
    have hPeq : P = q.asIdeal :=
      congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hPmem)
    subst P
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    have hxlocal : algebraMap A R x ∈ (I ⊔ J).map (algebraMap A R) := by
      rw [hlocal]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R q.asIdeal x).mpr hx
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) (I ⊔ J) x).mpr
        ((IsLocalization.algebraMap_mem_map_algebraMap_iff q.asIdeal.primeCompl
          R (I ⊔ J) x).mp hxlocal)
  · obtain ⟨x, hxK, hxP⟩ := Set.not_subset.mp hKP
    have htop : (I ⊔ J).map (algebraMap A (Localization.AtPrime P)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _
        (Ideal.mem_map_of_mem _ hxK)
        (IsLocalization.map_units (Localization.AtPrime P) (⟨x, hxP⟩ : P.primeCompl))
    rw [htop]
    exact le_top

/-- The actual tree gives a leaf whose original affine intersection is
reduced whenever its two original branch germs are transverse in the
actual scheme stalk. Singleton support is derived before transversality
is used, and all ideal maps below are the original section-germ maps. -/
theorem exists_component_leaf_transverse_quotient
    (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
    [Nontrivial ↥(irreducibleComponents X)]
    (hfinite : (componentIntersectionPoints X).Finite)
    (hTree : (componentPointIncidenceGraph X).IsTree) :
    ∃ (C : ↥(irreducibleComponents X)) (q : X),
      C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q} ∧
      ∀ (U : X.affineOpens) (hq : q ∈ U.1)
        (w : Fin 2 → maximalIdeal (X.presheaf.stalk q)),
        (w 0 : X.presheaf.stalk q) ∈
            (componentChartIdeal X {C} U).map (X.presheaf.germ U.1 q hq).hom →
        (w 1 : X.presheaf.stalk q) ∈
            (componentChartIdeal X ({C}ᶜ) U).map (X.presheaf.germ U.1 q hq).hom →
        Module.finrank (ResidueField (X.presheaf.stalk q))
            (CotangentSpace (X.presheaf.stalk q)) = 2 →
        LinearIndependent (ResidueField (X.presheaf.stalk q))
            (fun i => (maximalIdeal (X.presheaf.stalk q)).toCotangent (w i)) →
        componentChartIdeal X {C} U ⊔ componentChartIdeal X ({C}ᶜ) U =
            (U.2.primeIdealOf ⟨q, hq⟩).asIdeal ∧
          _root_.IsReduced
            (Γ(X, U.1) ⧸ (componentChartIdeal X {C} U ⊔
              componentChartIdeal X ({C}ᶜ) U)) := by
  obtain ⟨C, q, hcut, hcharts⟩ := exists_component_leaf_chart_support X hfinite hTree
  refine ⟨C, q, hcut, ?_⟩
  intro U hq w hw0 hw1 hdim hind
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk q) :=
    X.presheaf.algebra_section_stalk ⟨q, hq⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk q)
      (U.2.primeIdealOf ⟨q, hq⟩).asIdeal := U.2.isLocalization_stalk ⟨q, hq⟩
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing (X.presheaf.stalk q) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨q, hq⟩).asIdeal.primeCompl
      (X.presheaf.stalk q) inferInstance
  have hEq := nodeIdeal_eq_of_transverse_localization Γ(X, U.1)
    (componentChartIdeal X {C} U) (componentChartIdeal X ({C}ᶜ) U)
    (U.2.primeIdealOf ⟨q, hq⟩) (hcharts U hq)
    (X.presheaf.stalk q) w hw0 hw1 hdim hind
  refine ⟨hEq, ?_⟩
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  rw [hEq]
  exact (U.2.primeIdealOf ⟨q, hq⟩).isPrime.isRadical

end KltDP.Geometry.RationalTreePicard
