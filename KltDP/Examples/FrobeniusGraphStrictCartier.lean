import KltDP.Examples.FrobeniusGraphZeroCartier
import KltDP.Examples.FrobeniusStrictTransformClassesTower
import KltDP.Examples.FrobeniusStrictTransformProductCover
import KltDP.Examples.FrobeniusTowerFunctionField
import KltDP.Geometry.GluedIdealSheafKernel
import KltDP.Geometry.EffectiveCartierOfInvertibleIdeal

/-!
# The strict transform `B̃` of the graph as an effective Cartier divisor on every stage

Item 1 of BRIEF38, and the direct analogue of the accepted `fiberStrictIdeal_locallyPrincipalRegular`
/ `fiberStrictDivisor` for the strict *graph* instead of the strict fibre.

The accepted `strictTransformIdeal n (m + n)` is shown locally principal with regular generators on
every stage, by induction over the stages against the accepted three-piece cover
`strictProductStage_cover`:

* **stage `0`** is the graph itself: the accepted `graph_ker_eq_strictTransformIdeal_zero` identifies
  `strictTransformIdeal 0 p` with `(projectiveGraphMorphism p).ker = graphIdeal p`, so BRIEF37's
  `graphIdeal_locallyPrincipalRegular` is exactly the base case;
* on the **selected chart open** the generator is the accepted `firstAmbientEquation (n+1) m`
  (`strictIdeal_firstAffineOpen`, `firstAmbientEquation_regular`);
* on the **second Rees open** the generator is the accepted `secondAmbientEquation n m`
  (`strictIdeal_secondAffineOpen`, `secondAmbientEquation_regular`) — the residual equation
  `1 - u'^{m+1} v^m`, which is *not* a unit there and is precisely why the strict graph is present on
  that open where the strict fibre is absent (BRIEF37);
* over the **centre complement** the ideal is the transport of the stage-`n` ideal along the
  restricted blowdown, from the accepted `strictStepOnPuncture_ideal` through `ker_gluedTo` and the
  pinned `Scheme.ker_morphismRestrict_ideal`; the induction hypothesis is applied at `(n, m+1)`,
  matching the accepted index convention `m + (n + 1) = (m + 1) + n`.

`cartierDivisorOfIdeal` then produces `graphStrictDivisor` with its regular equations for free, and
its zero scheme is the strict transform.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphStrictCartier

open KltDP.Geometry
open AlgebraicGeometry.Scheme.IdealSheafData
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusGraphPicardClassAffine FrobeniusGraphPicardClassIntegral
open FrobeniusGraphZeroCartier
open FrobeniusStrictTransformClassesTower
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformSecondChartFrame
open FrobeniusStrictTransformStepPuncture FrobeniusStrictTransformProductCover

variable {k : Type u} [Field k]

local instance graphStrictInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

/-! ### Two elementary ring-isomorphism transports -/

/-- The comap of a principal ideal along an inverse isomorphism (the accepted helper of
`FrobeniusFiberStrictCartier`, restated to avoid importing the fibre tower). -/
private theorem comap_inv_span' {R S : CommRingCat.{u}} (i : R ≅ S) (g : R) :
    (Ideal.span {g}).comap i.inv.hom = Ideal.span {i.hom g} := by
  let σ := i.commRingCatIsoToRingEquiv
  change (Ideal.span {g}).comap (σ.symm : S →+* R) = Ideal.span {σ g}
  rw [Ideal.comap_coe, ← Ideal.map_symm, RingEquiv.symm_symm, Ideal.map_span, Set.image_singleton]

/-- Nonzerodivisors are preserved by a ring isomorphism. -/
private theorem regular_of_iso'' {R S : CommRingCat.{u}} (i : R ≅ S) (g : R)
    (hg : g ∈ nonZeroDivisors R) : i.hom g ∈ nonZeroDivisors S := by
  let σ := i.commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := σ.symm) σ.symm.injective
  change σ.symm (σ g) ∈ nonZeroDivisors R
  simpa only [σ.symm_apply_apply] using hg

/-! ### Stage `0` is the graph -/

/-- At stage `0` the strict transform is the graph, so BRIEF37's base-level statement applies. -/
theorem strictTransformIdeal_zero_locallyPrincipalRegular (p : ℕ) :
    IdealLocallyPrincipalRegular (strictTransformIdeal (k := k) 0 p) := by
  have h := graphIdeal_locallyPrincipalRegular (k := k) p
  rwa [show graphIdeal (k := k) p = strictTransformIdeal (k := k) 0 p from
    graph_ker_eq_strictTransformIdeal_zero p] at h

/-! ### Transport over the centre complement -/

/-- The blowdown restricted over the centre complement (an isomorphism). -/
abbrev graphPunctureIso (n : ℕ) :
    (nextPuncture (k := k) n).toScheme ⟶ (currentPuncture (k := k) n).toScheme :=
  (projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n

/-- Over the centre complement the strict-graph ideal of stage `n+1` is the transport of the
strict-graph ideal of stage `n` along the restricted blowdown. -/
theorem strictIdeal_puncture_transport (n m : ℕ)
    (W : (nextPuncture (k := k) n).toScheme.affineOpens) :
    (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal
        ⟨(nextPuncture n).ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩ =
      ((strictTransformIdeal (k := k) n ((m + 1) + n)).ideal
          ⟨(currentPuncture n).ι ''ᵁ (graphPunctureIso n ''ᵁ W.1),
            (W.2.image_of_isOpenImmersion (graphPunctureIso n)).image_of_isOpenImmersion _⟩).comap
        ((graphPunctureIso n).appIso W.1).inv.hom := by
  rw [← ker_gluedTo (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))),
    ← ker_gluedTo (strictTransformIdeal (k := k) n ((m + 1) + n)),
    ← Scheme.ker_morphismRestrict_ideal _ (nextPuncture n) W,
    ← Scheme.ker_morphismRestrict_ideal _ (currentPuncture n)
      ⟨graphPunctureIso n ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩]
  exact strictStepOnPuncture_ideal n m W

/-- A principal regular chart of the stage-`n` ideal containing the image of an affine open gives a
principal regular generator of the stage-`n+1` ideal on its image. -/
theorem strictIdeal_puncture_chart (n m : ℕ)
    (W : (nextPuncture (k := k) n).toScheme.affineOpens) [Nonempty W.1]
    (c : PrincipalRegularChart (projectiveContactStage (k := k) n)
      (strictTransformIdeal n ((m + 1) + n)))
    (hle : (currentPuncture n).ι ''ᵁ (graphPunctureIso n ''ᵁ W.1) ≤ c.openSet.1) :
    (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal
        ⟨(nextPuncture n).ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩ =
      Ideal.span {((graphPunctureIso n).appIso W.1).hom
        ((projectiveContactStage (k := k) n).presheaf.map (homOfLE hle).op c.generator)} ∧
    ((graphPunctureIso n).appIso W.1).hom
        ((projectiveContactStage (k := k) n).presheaf.map (homOfLE hle).op c.generator) ∈
      nonZeroDivisors Γ(projectiveContactStage (k := k) (n + 1), (nextPuncture n).ι ''ᵁ W.1) := by
  haveI : Nonempty ((currentPuncture (k := k) n).ι ''ᵁ (graphPunctureIso n ''ᵁ W.1) :
      (projectiveContactStage (k := k) n).Opens) := by
    obtain ⟨w⟩ := (inferInstance : Nonempty W.1)
    exact ⟨⟨(currentPuncture n).ι.base ((graphPunctureIso n).base w.1),
      ⟨_, ⟨w.1, w.2, rfl⟩, rfl⟩⟩⟩
  have hspan := c.restrict_span_eq
    ⟨(currentPuncture n).ι ''ᵁ (graphPunctureIso n ''ᵁ W.1),
      (W.2.image_of_isOpenImmersion (graphPunctureIso n)).image_of_isOpenImmersion _⟩ hle
  have hreg := (c.restrict
    ⟨(currentPuncture n).ι ''ᵁ (graphPunctureIso n ''ᵁ W.1),
      (W.2.image_of_isOpenImmersion (graphPunctureIso n)).image_of_isOpenImmersion _⟩ hle).regular
  refine ⟨?_, regular_of_iso'' _ _ hreg⟩
  rw [strictIdeal_puncture_transport n m W, hspan]
  exact comap_inv_span' ((graphPunctureIso n).appIso W.1) _

/-! ### Local principal regular generators on every stage -/

set_option maxHeartbeats 4000000 in
/-- **The strict-graph ideal sheaf is locally principal with regular generators on every stage.** -/
theorem strictTransformIdeal_locallyPrincipalRegular :
    ∀ n m : ℕ, IdealLocallyPrincipalRegular (strictTransformIdeal (k := k) n (m + n))
  | 0, m => strictTransformIdeal_zero_locallyPrincipalRegular m
  | n + 1, m => by
    intro x
    rcases strictProductStage_cover n x with hx | hx | hx
    · exact ⟨firstAffineOpen (n + 1), hx, firstAmbientEquation (n + 1) m,
        strictIdeal_firstAffineOpen (n + 1) m, firstAmbientEquation_regular (n + 1) m⟩
    · exact ⟨secondAffineOpen n, hx, secondAmbientEquation n m,
        strictIdeal_secondAffineOpen n m, secondAmbientEquation_regular n m⟩
    · obtain ⟨x', hx'⟩ : ∃ x' : (nextPuncture (k := k) n).toScheme,
          (nextPuncture n).ι.base x' = x := by
        have hr : x ∈ Set.range (nextPuncture (k := k) n).ι.base := by
          rw [Scheme.Opens.range_ι]
          exact hx
        exact hr
      obtain ⟨U', hxU', d, hd, hdr⟩ := strictTransformIdeal_locallyPrincipalRegular n (m + 1)
        (((projectiveProductInitial (k := k)).stepProjection n).base x)
      have hmem : x' ∈ graphPunctureIso n ⁻¹ᵁ ((currentPuncture (k := k) n).ι ⁻¹ᵁ U'.1) := by
        change (currentPuncture (k := k) n).ι.base ((graphPunctureIso n).base x') ∈ U'.1
        rw [← Scheme.comp_base_apply, morphismRestrict_ι, Scheme.comp_base_apply]
        change ((projectiveProductInitial (k := k)).stepProjection n).base
          ((nextPuncture n).ι.base x') ∈ U'.1
        rw [hx']
        exact hxU'
      obtain ⟨_, ⟨Wp, hWp, rfl⟩, hxW, hWle⟩ :=
        (isBasis_affine_open (nextPuncture (k := k) n).toScheme).exists_subset_of_mem_open hmem
          (graphPunctureIso n ⁻¹ᵁ ((currentPuncture (k := k) n).ι ⁻¹ᵁ U'.1)).2
      haveI : Nonempty Wp := ⟨⟨x', hxW⟩⟩
      have hle : (currentPuncture (k := k) n).ι ''ᵁ (graphPunctureIso n ''ᵁ Wp) ≤ U'.1 := by
        rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        exact hWle hz
      obtain ⟨hspan, hreg⟩ := strictIdeal_puncture_chart n m ⟨Wp, hWp⟩
        ⟨U', ⟨⟨_, hxU'⟩⟩, d, hd, hdr⟩ hle
      exact ⟨⟨(nextPuncture n).ι ''ᵁ Wp, hWp.image_of_isOpenImmersion _⟩, ⟨x', hxW, hx'⟩, _,
        hspan, hreg⟩

/-! ### The effective Cartier divisor -/

/-- **The strict transform `B̃` of the graph as an effective Cartier divisor on stage `n`.** -/
def graphStrictDivisor (n m : ℕ) : CartierDivisor (projectiveContactStage (k := k) n) :=
  cartierDivisorOfIdeal _ (strictTransformIdeal n (m + n))
    (strictTransformIdeal_locallyPrincipalRegular n m)

theorem graphStrictDivisor_hasRegularEquations (n m : ℕ) :
    HasRegularCartierEquations _ (graphStrictDivisor (k := k) n m) :=
  cartierDivisorOfIdeal_hasRegularEquations _ _ _

/-- Its zero scheme is the strict transform: the ideal-sheaf data is `strictTransformIdeal`. -/
theorem graphStrictDivisor_idealData (n m : ℕ) :
    effectiveCartierIdealDataOfRegularEquations _ (graphStrictDivisor (k := k) n m)
        (graphStrictDivisor_hasRegularEquations n m) =
      strictTransformIdeal (k := k) n (m + n) :=
  cartierDivisorOfIdeal_idealData _ _ _

end KltDP.Examples.FrobeniusGraphStrictCartier
