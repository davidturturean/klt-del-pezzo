import KltDP.Geometry.PointBlowupSNCBoundaryParameters
import KltDP.Geometry.PointBlowupReducedBoundaryChartSNC
import KltDP.Geometry.AffineBlowupCover

/-!
# An actual reduced-boundary SNC cover from the original SNC germ

The original SNC germ determines the boundary-adapted parameters. They
cover the original localized Rees scheme by the already proved ideal-
generator cover theorem. On both actual charts the original reduced
exceptional-plus-pullback ideal has one equation that is SNC at every
point above the centre. No chosen-coordinate or equation-factorization
hypothesis remains in this conclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open AffineBlowup LocalizedParameterReesChart

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
variable {R : Type u} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]

/-- The original SNC germ supplies a covering pair of actual parameter
charts with derived reduced ideal equations and SNC at all exceptional points. -/
theorem pointBlowup_snc_reduced_chart_cover
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (c : Localization.AtPrime q.asIdeal)
    (hc : IsStrictNormalCrossingsEquation (Localization.AtPrime q.asIdeal) c) :
    ∃ f g : localCenter q.asIdeal,
      Ideal.span {(f : Localization.AtPrime q.asIdeal),
        (g : Localization.AtPrime q.asIdeal)} = localCenter q.asIdeal ∧
      chartOpen (localCenter q.asIdeal) f ⊔ chartOpen (localCenter q.asIdeal) g = ⊤ ∧
      ∀ d : localCenter q.asIdeal, d = f ∨ d = g →
        ∃ e : chartRing (localCenter q.asIdeal) d,
          (chartCenterIdeal (localCenter q.asIdeal) d *
            Ideal.map (chartBaseMap (localCenter q.asIdeal) d) (Ideal.span {c})).radical =
            Ideal.span {e} ∧
          ∀ (P : Ideal (chartRing (localCenter q.asIdeal) d)) [P.IsPrime],
            chartCenterIdeal (localCenter q.asIdeal) d ≤ P →
            IsStrictNormalCrossingsEquation (Localization.AtPrime P)
              (algebraMap (chartRing (localCenter q.asIdeal) d) (Localization.AtPrime P) e) := by
  obtain ⟨f, g, hfg, hc'⟩ := X.pointBlowup_snc_boundary_parameters j q hclosed c hc
  have hspan : Ideal.span (Set.range (fun i : Fin 2 =>
      (![f, g] i : Localization.AtPrime q.asIdeal))) = localCenter q.asIdeal := by
    have hfun : (fun i : Fin 2 => (![f, g] i : Localization.AtPrime q.asIdeal)) =
        ![(f : Localization.AtPrime q.asIdeal), (g : Localization.AtPrime q.asIdeal)] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun, Matrix.range_cons_cons_empty]
    exact hfg
  have hcover : chartOpen (localCenter q.asIdeal) f ⊔
      chartOpen (localCenter q.asIdeal) g = ⊤ := by
    apply top_unique
    rw [← iSup_chartOpen_generators (localCenter q.asIdeal) ![f, g] hspan]
    apply iSup_le
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  refine ⟨f, g, hfg, hcover, ?_⟩
  intro d hd
  rcases hd with hdf | hdg
  · subst d
    apply X.pointBlowup_reduced_boundary_chart_snc j q hclosed f g hfg c
    rcases hc' with hu | ⟨v, hfirst | hpair⟩
    · exact Or.inl hu
    · exact Or.inr ⟨v, Or.inl hfirst⟩
    · exact Or.inr ⟨v, Or.inr (Or.inr hpair)⟩
  · subst d
    apply X.pointBlowup_reduced_boundary_chart_snc j q hclosed g f
      (Ideal.span_pair_comm.trans hfg) c
    rcases hc' with hu | ⟨v, hfirst | hpair⟩
    · exact Or.inl hu
    · exact Or.inr ⟨v, Or.inr (Or.inl hfirst)⟩
    · refine Or.inr ⟨v, Or.inr (Or.inr ?_)⟩
      simpa only [mul_comm (f : Localization.AtPrime q.asIdeal)
        (g : Localization.AtPrime q.asIdeal)] using hpair

end KltDP.Geometry.NormalProjectiveSurface
