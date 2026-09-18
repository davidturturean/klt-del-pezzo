import KltDP.Geometry.PointBlowupParameterChartAllSNC
import KltDP.Geometry.StrictNormalCrossingsSurfaceEquation

/-!
# Boundary-adapted parameters from the original SNC germ

An arbitrary SNC germ at the actual smooth closed centre supplies a
maximal-ideal generating pair adapted to its one or two branches. In the
unit case an actual regular parameter pair is obtained from the centre's
proved regularity and dimension. No identification with an unrelated
étale coordinate system is made or assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry

private theorem exists_pair_in_maximal_ideal {A : Type u} [CommRing A] [IsLocalRing A]
    (hA : RegularLocal A) (hdim : ringKrullDim A = 2)
    (I : Ideal A) (hI : I = maximalIdeal A) :
    ∃ f g : I, Ideal.span {(f : A), (g : A)} = I := by
  obtain ⟨d, t, hd, ht⟩ := regularLocal_exists_dimension_generators hA
  have hd2 : d = 2 := by exact_mod_cast hd.symm.trans hdim
  subst d
  have htfun : (fun i => (t i : A)) = ![(t 0 : A), (t 1 : A)] := by
    funext i
    fin_cases i <;> rfl
  refine ⟨⟨t 0, hI.symm ▸ (t 0).property⟩, ⟨t 1, hI.symm ▸ (t 1).property⟩, ?_⟩
  change Ideal.span {(t 0 : A), (t 1 : A)} = I
  have hpair : Ideal.span {(t 0 : A), (t 1 : A)} = maximalIdeal A := by
    simpa only [htfun, Matrix.range_cons_cons_empty] using ht
  exact hpair.trans hI.symm

namespace NormalProjectiveSurface

open LocalizedParameterReesChart

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
variable {R : Type u} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]

/-- The original SNC germ itself produces the actual adapted parameter
pair in the localized original centre ideal. -/
theorem pointBlowup_snc_boundary_parameters
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (c : Localization.AtPrime q.asIdeal)
    (hc : IsStrictNormalCrossingsEquation (Localization.AtPrime q.asIdeal) c) :
    ∃ f g : localCenter q.asIdeal,
      Ideal.span {(f : Localization.AtPrime q.asIdeal),
        (g : Localization.AtPrime q.asIdeal)} = localCenter q.asIdeal ∧
      (IsUnit c ∨ ∃ v : (Localization.AtPrime q.asIdeal)ˣ,
        c = (v : Localization.AtPrime q.asIdeal) * f ∨
        c = (v : Localization.AtPrime q.asIdeal) * (f * g)) := by
  have hmax : localCenter q.asIdeal = maximalIdeal (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)
  let e := openImmersionStalkLocalizationEquiv j q
  have hA : RegularLocal (Localization.AtPrime q.asIdeal) :=
    regularLocal_of_ringEquiv e (X.regularPoints_of_isSmooth (j.base q))
  have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 2 :=
    (ringKrullDim_eq_of_ringEquiv e).symm.trans
      (X.closed_stalk_dimension_two (j.base q) hclosed)
  rcases hc.surface_equation hdim with hu | ⟨f, g, v, _, hspan, heq⟩
  · obtain ⟨f, g, hfg⟩ := exists_pair_in_maximal_ideal hA hdim (localCenter q.asIdeal) hmax
    exact ⟨f, g, hfg, Or.inl hu⟩
  · have hf : f ∈ localCenter q.asIdeal := by
      rw [hmax, ← hspan]
      exact Ideal.subset_span (by simp)
    have hg : g ∈ localCenter q.asIdeal := by
      rw [hmax, ← hspan]
      exact Ideal.subset_span (by simp)
    exact ⟨⟨f, hf⟩, ⟨g, hg⟩, hspan.trans hmax.symm, Or.inr ⟨v, heq⟩⟩

end NormalProjectiveSurface
end KltDP.Geometry
