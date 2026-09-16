import KltDP.Examples.FrobeniusOldExceptionalBirthCartier
import KltDP.Examples.FrobeniusExceptionalCartierPicard
import KltDP.Examples.FrobeniusOldExceptionalLaterStages

/-!
# The older exceptional curves `C_j` on every later stage as effective Cartier divisors

On every stage `N ≥ j+2` of the origin contact tower, the embedded image of `C_j` (lane A2's closed
immersion `oldFinalMap N j h`) has a locally principal regular ideal sheaf `oldFinalIdeal N j h`
(`oldFinalIdeal_locallyPrincipalRegular`): stage `N` is covered by the iso locus (the preimage of
the centre complement of the birth stage, where the composite blowdown `oldBetween N j h` is an
isomorphism) and the away locus (the preimage of the complement of `C_j`), by lane A2's
`oldLoci_cover`. Over the away locus the ideal is the unit ideal (`C_j` lies over the iso locus,
`oldFinalIdeal_away`); over the iso locus it is the transport of the birth-stage ideal
`oldStrictIdeal j` along the restricted blowdown, by lane A2's square `oldLocusMap_square` (both
vertical maps isomorphisms, hence a pullback square `oldFinalMap_isPullback`) and the pinned
`ker_ideal_of_isPullback_of_isOpenImmersion`/`ker_morphismRestrict_ideal`
(`oldFinalIdeal_locus_transport`).

Hence `oldFinalDivisor N j h : CartierDivisor (projectiveContactStage k N)` is an effective
Cartier divisor with regular equations, its ideal-sheaf data is `oldFinalIdeal N j h` (zero scheme:
the glued closed subscheme of the kernel of `oldFinalMap`), and its Cartier class is lane A2's
`oldExceptionalStrictClass N j h` (`oldFinalDivisor_picard`, through the public kernel
comparison `toPic_eq_gluedKernelLine`). Bundle `f29_old_exceptional_cartier` with a universe check.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalLaterCartier

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusOldExceptionalChartIdeals
  FrobeniusOldExceptionalLaterStages FrobeniusOldExceptionalBirthCartier
  FrobeniusExceptionalCartier FrobeniusFiberStrictCartier FrobeniusStrictTransformStepPuncture
  FrobeniusTowerFunctionField FrobeniusGraphPicardClassIntegral FrobeniusBlowupChartIteration

variable {k : Type u} [Field k]

local instance initialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

local instance originMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

local instance oldStrict_restrict_isClosedImmersion (j : ℕ) :
    IsClosedImmersion (oldExceptionalStrictι (k := k) j ∣_ oldCentreComplement j) :=
  IsLocalAtTarget.restrict (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion (oldExceptionalStrictι (k := k) j)) _

/-- The ideal sheaf of the embedded image of `C_j` on stage `N`. -/
abbrev oldFinalIdeal (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (projectiveContactStage (k := k) N).IdealSheafData :=
  (oldFinalMap (k := k) N j h).ker

/-- The composite blowdown restricted to the centre complement of the birth stage (an
isomorphism from the iso locus). -/
abbrev locusIso (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    (oldIsoLocus (k := k) N j h).toScheme ⟶ (oldCentreComplement (k := k) j).toScheme :=
  oldBetween (k := k) N j h ∣_ oldCentreComplement j

/-- Lane A2's square over the iso locus is a pullback square (both vertical maps are
isomorphisms). -/
theorem oldFinalMap_isPullback (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    IsPullback (oldFinalMap (k := k) N j h ∣_ oldIsoLocus N j h) (oldLocusMap N j h)
      (locusIso N j h) (oldExceptionalStrictι (k := k) j ∣_ oldCentreComplement j) :=
  IsPullback.of_vert_isIso ⟨oldLocusMap_square N j h⟩

/-! ## The away locus -/

/-- `C_j` misses every open inside the away locus. -/
theorem oldFinalMap_preimage_away (N j : ℕ) (h : j + 1 + 1 ≤ N)
    (W : (projectiveContactStage (k := k) N).Opens) (hW : W ≤ oldAwayLocus N j h) :
    oldFinalMap (k := k) N j h ⁻¹ᵁ W = ⊥ := by
  apply Opens.ext
  rw [Opens.coe_bot]
  refine Set.eq_empty_iff_forall_not_mem.mpr fun z hz => ?_
  have hx : (oldFinalMap (k := k) N j h).base z ∈ oldAwayLocus N j h := hW hz
  exact hx ⟨z, by rw [← Scheme.comp_base_apply, oldFinalMap_between]⟩

/-- On every affine open inside the away locus the ideal of `C_j` is the unit ideal. -/
theorem oldFinalIdeal_away (N j : ℕ) (h : j + 1 + 1 ≤ N)
    (W : (projectiveContactStage (k := k) N).affineOpens) (hW : W.1 ≤ oldAwayLocus N j h) :
    (oldFinalIdeal (k := k) N j h).ideal W =
      Ideal.span {(1 : Γ(projectiveContactStage (k := k) N, W.1))} :=
  ker_ideal_eq_top_of_preimage_eq_bot (oldFinalMap (k := k) N j h) W
    (oldFinalMap_preimage_away N j h W.1 hW)

/-! ## The iso locus -/

/-- Over the iso locus, the ideal of `C_j` on stage `N` is the transport of its birth-stage ideal
along the restricted blowdown. -/
theorem oldFinalIdeal_locus_transport (N j : ℕ) (h : j + 1 + 1 ≤ N)
    (W : (oldIsoLocus (k := k) N j h).toScheme.affineOpens) :
    (oldFinalIdeal (k := k) N j h).ideal
        ⟨(oldIsoLocus N j h).ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩ =
      ((oldStrictIdeal (k := k) j).ideal
          ⟨(oldCentreComplement j).ι ''ᵁ (locusIso N j h ''ᵁ W.1),
            (W.2.image_of_isOpenImmersion (locusIso N j h)).image_of_isOpenImmersion _⟩).comap
        ((locusIso N j h).appIso W.1).inv.hom := by
  rw [← Scheme.ker_morphismRestrict_ideal _ (oldIsoLocus N j h) W,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _ (oldFinalMap_isPullback N j h) W]
  congr 1
  exact Scheme.ker_morphismRestrict_ideal (oldExceptionalStrictι (k := k) j)
    (oldCentreComplement j) ⟨locusIso N j h ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩

/-- A principal regular chart of the birth-stage ideal containing the image of an affine open `W`
of the iso locus gives a principal regular generator of the stage-`N` ideal on the image of `W`. -/
theorem oldFinalIdeal_locus_chart (N j : ℕ) (h : j + 1 + 1 ≤ N)
    (W : (oldIsoLocus (k := k) N j h).toScheme.affineOpens) [Nonempty W.1]
    (c : PrincipalRegularChart (projectiveContactStage (k := k) (j + 1 + 1)) (oldStrictIdeal j))
    (hle : (oldCentreComplement j).ι ''ᵁ (locusIso N j h ''ᵁ W.1) ≤ c.openSet.1) :
    (oldFinalIdeal (k := k) N j h).ideal
        ⟨(oldIsoLocus N j h).ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩ =
      Ideal.span {((locusIso N j h).appIso W.1).hom
        ((projectiveContactStage (k := k) (j + 1 + 1)).presheaf.map (homOfLE hle).op
          c.generator)} ∧
    ((locusIso N j h).appIso W.1).hom
        ((projectiveContactStage (k := k) (j + 1 + 1)).presheaf.map (homOfLE hle).op
          c.generator) ∈
      nonZeroDivisors Γ(projectiveContactStage (k := k) N, (oldIsoLocus N j h).ι ''ᵁ W.1) := by
  haveI : Nonempty ((oldCentreComplement (k := k) j).ι ''ᵁ (locusIso N j h ''ᵁ W.1) :
      (projectiveContactStage (k := k) (j + 1 + 1)).Opens) := by
    obtain ⟨w⟩ := (inferInstance : Nonempty W.1)
    exact ⟨⟨(oldCentreComplement j).ι.base ((locusIso N j h).base w.1),
      ⟨_, ⟨w.1, w.2, rfl⟩, rfl⟩⟩⟩
  have hspan := c.restrict_span_eq
    ⟨(oldCentreComplement j).ι ''ᵁ (locusIso N j h ''ᵁ W.1),
      (W.2.image_of_isOpenImmersion (locusIso N j h)).image_of_isOpenImmersion _⟩ hle
  have hreg := (c.restrict
    ⟨(oldCentreComplement j).ι ''ᵁ (locusIso N j h ''ᵁ W.1),
      (W.2.image_of_isOpenImmersion (locusIso N j h)).image_of_isOpenImmersion _⟩ hle).regular
  refine ⟨?_, regular_of_iso _ _ hreg⟩
  rw [oldFinalIdeal_locus_transport N j h W, hspan]
  exact comap_inv_span ((locusIso N j h).appIso W.1) _

/-- The ideal sheaf of `C_j` on every stage `N ≥ j+2` is locally principal with regular
generators. -/
theorem oldFinalIdeal_locallyPrincipalRegular (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    IdealLocallyPrincipalRegular (oldFinalIdeal (k := k) N j h) := by
  intro x
  rcases oldLoci_cover N j h x with hx | hx
  · obtain ⟨x', hx'⟩ : ∃ x' : (oldIsoLocus (k := k) N j h).toScheme,
        (oldIsoLocus N j h).ι.base x' = x := by
      have hr : x ∈ Set.range (oldIsoLocus (k := k) N j h).ι.base := by
        rw [Scheme.Opens.range_ι]
        exact hx
      exact hr
    obtain ⟨U', hxU', d, hd, hdr⟩ := oldStrictIdeal_locallyPrincipalRegular j
      ((oldBetween (k := k) N j h).base x)
    have hmem : x' ∈ locusIso N j h ⁻¹ᵁ ((oldCentreComplement (k := k) j).ι ⁻¹ᵁ U'.1) := by
      change (oldCentreComplement (k := k) j).ι.base ((locusIso N j h).base x') ∈ U'.1
      rw [← Scheme.comp_base_apply, morphismRestrict_ι, Scheme.comp_base_apply]
      change (oldBetween (k := k) N j h).base ((oldIsoLocus N j h).ι.base x') ∈ U'.1
      rw [hx']
      exact hxU'
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
      (isBasis_affine_open (oldIsoLocus (k := k) N j h).toScheme).exists_subset_of_mem_open hmem
        (locusIso N j h ⁻¹ᵁ ((oldCentreComplement (k := k) j).ι ⁻¹ᵁ U'.1)).2
    haveI : Nonempty W := ⟨⟨x', hxW⟩⟩
    have hle : (oldCentreComplement (k := k) j).ι ''ᵁ (locusIso N j h ''ᵁ W) ≤ U'.1 := by
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact hWle hz
    obtain ⟨hspan, hreg⟩ := oldFinalIdeal_locus_chart N j h ⟨W, hW⟩
      ⟨U', ⟨⟨_, hxU'⟩⟩, d, hd, hdr⟩ hle
    exact ⟨⟨(oldIsoLocus N j h).ι ''ᵁ W, hW.image_of_isOpenImmersion _⟩, ⟨x', hxW, hx'⟩, _,
      hspan, hreg⟩
  · obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
      (isBasis_affine_open (projectiveContactStage (k := k) N)).exists_subset_of_mem_open hx
        (oldAwayLocus (k := k) N j h).2
    exact ⟨⟨W, hW⟩, hxW, 1, oldFinalIdeal_away N j h ⟨W, hW⟩ hWle, Submonoid.one_mem _⟩

/-! ## The effective Cartier divisor -/

/-- `C_j` as an effective Cartier divisor on stage `N ≥ j+2`. -/
def oldFinalDivisor (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    CartierDivisor (projectiveContactStage (k := k) N) :=
  cartierDivisorOfIdeal _ (oldFinalIdeal N j h) (oldFinalIdeal_locallyPrincipalRegular N j h)

theorem oldFinalDivisor_hasRegularEquations (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    HasRegularCartierEquations (projectiveContactStage (k := k) N) (oldFinalDivisor N j h) :=
  cartierDivisorOfIdeal_hasRegularEquations _ _ _

/-- The ideal-sheaf data of the divisor is the kernel of `oldFinalMap N j h`. -/
theorem oldFinalDivisor_idealData (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    effectiveCartierIdealDataOfRegularEquations (projectiveContactStage (k := k) N)
        (oldFinalDivisor N j h) (oldFinalDivisor_hasRegularEquations N j h) =
      oldFinalIdeal N j h :=
  cartierDivisorOfIdeal_idealData _ _ _

/-- **`[C_j] = cartierPicardHom (oldFinalDivisor N j h)`**: the Cartier class of `C_j` on stage `N`
is lane A2's `oldExceptionalStrictClass N j h`. -/
theorem oldFinalDivisor_picard (N j : ℕ) (h : j + 1 + 1 ≤ N) :
    cartierPicardHom (projectiveContactStage (k := k) N) (oldFinalDivisor N j h) =
      oldExceptionalStrictClass N j h := by
  rw [oldFinalDivisor, cartierDivisorOfIdeal_picard]
  change -Additive.ofMul (gluedKernelLine (oldFinalIdeal (k := k) N j h)
      (oldFinalIdeal_locallyPrincipalRegular N j h)).toPic =
    -Additive.ofMul (oldFinalKernelLine (k := k) N j h).toPic
  rw [← toPic_eq_gluedKernelLine (oldFinalMap (k := k) N j h) (oldFinalKernel_isInvertible N j h)]
  rfl

end KltDP.Examples.FrobeniusOldExceptionalLaterCartier

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusOldExceptionalLaterStages
  FrobeniusOldExceptionalLaterCartier FrobeniusTowerFunctionField
  FrobeniusGraphPicardClassIntegral

local instance laterInitialIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

/-- Bundle: on every stage `N ≥ j+2` of the origin contact tower, the embedded image of the
exceptional curve `C_j` is an effective Cartier divisor with regular equations whose ideal-sheaf
data is the kernel of lane A2's closed immersion `oldFinalMap N j h`, with Cartier class lane A2's
`oldExceptionalStrictClass N j h`. -/
theorem f29_old_exceptional_cartier (k : Type u) [Field k] :
    ∀ (N j : ℕ) (h : j + 1 + 1 ≤ N),
      HasRegularCartierEquations (projectiveContactStage (k := k) N) (oldFinalDivisor N j h) ∧
      effectiveCartierIdealDataOfRegularEquations (projectiveContactStage (k := k) N)
          (oldFinalDivisor N j h) (oldFinalDivisor_hasRegularEquations N j h) =
        (oldFinalMap (k := k) N j h).ker ∧
      cartierPicardHom (projectiveContactStage (k := k) N) (oldFinalDivisor N j h) =
        oldExceptionalStrictClass N j h :=
  fun N j h => ⟨oldFinalDivisor_hasRegularEquations N j h, oldFinalDivisor_idealData N j h,
    oldFinalDivisor_picard N j h⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_old_exceptional_cartier_universe_check (k : Type u) [Field k] : True := by
  have _ := f29_old_exceptional_cartier.{u} k
  trivial

end KltDP.Examples
