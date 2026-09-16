import KltDP.Literature.ResolutionLiterals

/-!
# Existence of a minimal resolution, conditional on the Stacks literals (F10, first consumer)

`exists_minimalResolution`: given Lipman's theorem (0BGP), Castelnuovo's contraction (0C2N), the universal property of
contractions (0C5J) and a contraction-decreasing natural-number invariant (`ContractionMeasureHypothesis`, intended:
Picard rank via 0C5L), every `X : NormalProjectiveSurface k` with finite singular locus has a minimal resolution.

Proof: Lipman gives a resolution `π : S → X`; if it has an exceptional `(−1)`-curve `E`, Castelnuovo contracts `E`
to `b : S → S'`; the universal property factors `π = b ≫ π'` and identifies `π'` as a morphism over `k`
(uniqueness of the factorization of the structure morphism); `π'` is a resolution (regularity of `S'` from the
contraction, birationality by right cancellation); the invariant drops, so strong induction terminates.
All hypotheses are explicit; nothing is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k]

/-- The structure morphism to `Spec k` contracts every prime curve to the unique point of `Spec k`. -/
theorem structureMorphism_image_primeCurve_singleton (S : NormalProjectiveSurface k) (E : S.PrimeCurve) :
    ∃ y : Spec (CommRingCat.of k), S.structureMorphism.base '' (E : Set S.toScheme) = {y} := by
  letI : Subsingleton (Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  refine ⟨S.structureMorphism.base E.genericPoint, Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩⟩
  · exact Set.mem_image_of_mem _ E.genericPoint_mem
  · rintro z ⟨t, -, rfl⟩
    exact Subsingleton.elim _ _

/-- Contracting an exceptional `(−1)`-curve of a resolution yields a resolution of the same surface. -/
theorem IsResolution.of_contraction [IsAlgClosed k] (hU : ContractionUniversalLiteral k)
    {S S' X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme} (hπ : IsResolution S X π)
    {b : S.toScheme ⟶ S'.toScheme} {E : S.PrimeCurve} (hb : IsContraction S S' b E)
    (hE : IsExceptionalCurve π E) :
    ∃ π' : S'.toScheme ⟶ X.toScheme, b ≫ π' = π ∧ IsResolution S' X π' := by
  obtain ⟨π', hfac₀, -⟩ := hU.factor S S' b E hb X.toScheme π hE
  have hfac : b ≫ π' = π := hfac₀
  refine ⟨π', hfac, ?_, hb.regular, ?_⟩
  · obtain ⟨ψ, -, huniq⟩ := hU.factor S S' b E hb _ S.structureMorphism
      (structureMorphism_image_primeCurve_singleton S E)
    have h1 : π' ≫ X.structureMorphism = ψ := huniq (π' ≫ X.structureMorphism)
      (show b ≫ (π' ≫ X.structureMorphism) = S.structureMorphism by
        rw [← Category.assoc, hfac, hπ.over_base])
    have h2 : S'.structureMorphism = ψ := huniq S'.structureMorphism hb.over_base
    exact h1.trans h2.symm
  · refine IsBirational.of_comp hb.birational ?_
    rw [hfac]
    exact hπ.birational

/-- **Existence of a minimal resolution**, conditional on the named Stacks literals and the termination
hypothesis. -/
theorem exists_minimalResolution [IsAlgClosed k]
    (hL : LipmanResolutionLiteral k) (hC : CastelnuovoContractionLiteral k)
    (hU : ContractionUniversalLiteral k) (hμ : ContractionMeasureHypothesis k)
    (X : NormalProjectiveSurface k) (hfin : (singularLocus X.toScheme).Finite) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme), IsMinimalResolution S X π := by
  obtain ⟨μ, hμ⟩ := hμ.exists_measure
  obtain ⟨S₀, π₀, h₀⟩ := hL.exists_resolution X hfin
  suffices key : ∀ (n : ℕ) (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsResolution S X π → μ S = n →
        ∃ (S' : NormalProjectiveSurface k) (π' : S'.toScheme ⟶ X.toScheme),
          IsMinimalResolution S' X π' from
    key (μ S₀) S₀ π₀ h₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S π hπ hn
    by_cases hmin : ∀ C : S.PrimeCurve, IsExceptionalCurve π C → ¬ IsMinusOneCurve hπ.regular C
    · exact ⟨S, π, { toIsResolution := hπ, no_minusOne_curve := hmin }⟩
    · push_neg at hmin
      obtain ⟨E, hE, hE1⟩ := hmin
      obtain ⟨S', b, hb⟩ := hC.exists_contraction S hπ.regular E hE1
      obtain ⟨π', -, hres⟩ := hπ.of_contraction hU hb hE
      refine ih (μ S') ?_ S' π' hres rfl
      rw [← hn]
      exact hμ S S' b E hb

end KltDP.Geometry
