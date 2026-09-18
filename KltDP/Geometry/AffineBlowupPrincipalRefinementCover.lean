import KltDP.Geometry.AffineBlowupExceptionalIdealRefinement
import KltDP.Geometry.AffineBlowupCover

/-!
# Actual principal refinements of an original Rees generating cover

Choosing a principal neighborhood at every original chart prime still gives
an open-immersion cover of the original blowup. The point lifts are supplied
by the original generating affine cover and the pinned localization spectrum
range theorem. No new covering assumption is needed beyond `r ∉ p`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace KltDP.Geometry.AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R) {ι : Type v} (g : ι → I)
variable (r : ∀ i, PrimeSpectrum (chartRing I (g i)) → chartRing I (g i))

abbrev principalRefinementIndex := Σ i, PrimeSpectrum (chartRing I (g i))

/-- Each object is the literal spectrum of the chosen original localization. -/
def principalRefinementScheme (t : principalRefinementIndex I g) : Scheme.{u} :=
  Spec (CommRingCat.of (Localization.Away (r t.1 t.2)))

/-- Its actual map is localization followed by the original Rees chart map. -/
def principalRefinementMap (t : principalRefinementIndex I g) :
    principalRefinementScheme I g r t ⟶ scheme I :=
  refinedChartMap I (g t.1)
    (algebraMap (chartRing I (g t.1)) (Localization.Away (r t.1 t.2)))

instance principalRefinementMap_isOpenImmersion (t : principalRefinementIndex I g) :
    IsOpenImmersion (principalRefinementMap I g r t) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (chartRing I (g t.1)) (Localization.Away (r t.1 t.2))))) :=
    IsOpenImmersion.of_isLocalization (r t.1 t.2)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (chartRing I (g t.1)) (Localization.Away (r t.1 t.2)))) ≫ chartι I (g t.1))
  infer_instance

variable (hg : Ideal.span (Set.range (fun i => (g i : R))) = I)
variable (hr : ∀ i p, r i p ∉ p.asIdeal)

include hg hr in
/-- The original localization point lifts cover the original blowup. -/
theorem principalRefinementMap_jointly_surjective (x : scheme I) :
    ∃ t, ∃ y : principalRefinementScheme I g r t, (principalRefinementMap I g r t).base y = x := by
  obtain ⟨i, p, hp⟩ := (generatingAffineCover I g hg).openCover.exists_eq x
  change (chartι I (g i)).base p = x at hp
  have hmem : p ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (chartRing I (g i)) (Localization.Away (r i p)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (r i p)) (r i p)]
    exact hr i p
  obtain ⟨y, hy⟩ := hmem
  refine ⟨⟨i, p⟩, y, ?_⟩
  change (chartι I (g i)).base
    (PrimeSpectrum.comap (algebraMap (chartRing I (g i)) (Localization.Away (r i p))) y) = x
  exact (congrArg (chartι I (g i)).base hy).trans hp

end KltDP.Geometry.AffineBlowup
