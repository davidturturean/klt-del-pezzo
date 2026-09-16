import KltDP.Compatibility.QuotientIdealPullback
import KltDP.Geometry.QuadraticRamificationCharts

/-!
# Actual root-zero base change along the original quadratic atlas

The original coefficient and generator maps extend the actual root ideal.
The pinned quotient-tensor construction therefore makes their root-zero
square a pullback. In particular the actual frame maps are open immersions
with the required intersection ranges. Their identity and composition laws
are derived by cancellation of their actual closed inclusions in the cover.

These are gluing prerequisites on the original atlas. The file does not
assume or construct a global root-zero scheme as an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual root-zero square of every original rescaling map is a pullback. -/
theorem rootZeroSchemeMap_isPullback (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) :
    IsPullback (rootZeroι t) (rootZeroSchemeMap f s t v h)
      (mappedRescaleMap f s t v h) (rootZeroι s) :=
  KltDP.QuotientIdealPullback.isPullback (mappedRescaleHom f s t v h)
    (rootIdeal s) (rootIdeal t) (map_rootIdeal_mappedRescaleHom f s t v h)

end KltDP.Geometry.QuadraticCover

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- This pullback uses the original frame map, not a replacement map. -/
theorem rootZeroFrameMap_isPullback {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V) :
    IsPullback (rootZeroι (res X hj (D.sections j))) (D.rootZeroFrameMap hi hj hWV)
      (D.map hi hj hWV) (rootZeroι (res X hi (D.sections i))) :=
  rootZeroSchemeMap_isPullback _ _ _ _ _

/-- Affine frame restrictions induce actual open immersions on the root-zero schemes. -/
theorem rootZeroFrameMap_isOpenImmersion {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    IsOpenImmersion (D.rootZeroFrameMap hi hj hWV) := by
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (D.rootZeroFrameMap_isPullback hi hj hWV) (D.map_isOpenImmersion hi hj hWV hV hW)

/-- The original root-zero frame maps satisfy the original restriction composition law. -/
@[reassoc]
theorem rootZeroFrameMap_comp {i j k : ι} {V W Z : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hk : Z ≤ D.opens k)
    (hWV : W ≤ V) (hZW : Z ≤ W) :
    D.rootZeroFrameMap hj hk hZW ≫ D.rootZeroFrameMap hi hj hWV =
      D.rootZeroFrameMap hi hk (hZW.trans hWV) := by
  apply (cancel_mono (rootZeroι (res X hi (D.sections i)))).mp
  simp only [Category.assoc, rootZeroFrameMap_ι, rootZeroFrameMap_ι_assoc, map_comp]

/-- The identity frame map induces the identity on the actual root-zero scheme. -/
@[simp]
theorem rootZeroFrameMap_self {i : ι} {W : X.Opens}
    (hi : W ≤ D.opens i) (hWW : W ≤ W) :
    D.rootZeroFrameMap hi hi hWW = 𝟙 (rootZeroScheme (res X hi (D.sections i))) := by
  apply (cancel_mono (rootZeroι (res X hi (D.sections i)))).mp
  simp only [rootZeroFrameMap_ι, map_self, Category.comp_id, Category.id_comp]

/-- The actual image of a root-zero frame is the inverse image of its original base open. -/
theorem range_rootZeroFrameMap {i j : ι} {V W : X.Opens}
    (hi : V ≤ D.opens i) (hj : W ≤ D.opens j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    Set.range (D.rootZeroFrameMap hi hj hWV).base =
      (rootZeroι (res X hi (D.sections i)) ≫ D.frameToBase hi hV).base ⁻¹'
        (W : Set X) := by
  let hp := D.rootZeroFrameMap_isPullback hi hj hWV
  have he : Function.Surjective hp.isoPullback.hom.base := by
    rw [← TopCat.epi_iff_surjective]
    infer_instance
  rw [← hp.isoPullback_hom_snd, Scheme.comp_base, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.mpr he, Set.image_univ,
    Scheme.Pullback.range_snd, D.range_map hi hj hWV hV hW]
  rfl

end KltDP.Geometry.QuadraticCoverAtlas.Data
