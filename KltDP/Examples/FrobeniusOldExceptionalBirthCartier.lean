import KltDP.Examples.FrobeniusExceptionalCartier
import KltDP.Examples.FrobeniusFiberStrictCartier
import KltDP.Examples.FrobeniusOldExceptionalPuncture

/-!
# The older exceptional curve `C_j` on its birth stage as an effective Cartier divisor

On stage `j+2` of the origin contact tower, the strict transform `C_j` of the exceptional curve
`E_j` (lane A2's closed immersion `oldExceptionalStrictι j`) has a locally principal regular ideal
sheaf `oldStrictIdeal j` (`oldStrictIdeal_locallyPrincipalRegular`): on the selected chart open it
is absent (accepted `oldStrictIdeal_firstAffineOpen`), on the second Rees open it is cut out by the
ratio coordinate (accepted `oldStrictIdeal_secondAffineOpen`, regular by
`oldStrictSecondAmbientEquation_regular`), and over the centre complement it is the transport of
the ideal of `E_j = P` on stage `j+1` (`FrobeniusExceptionalCartier.stepExceptionalIdeal j`) along
the restricted blowdown, by lane A2's pullback square `oldStrictOnPuncture_isPullback` and the
pinned `ker_ideal_of_isPullback_of_isOpenImmersion`/`ker_morphismRestrict_ideal`
(`oldStrictIdeal_puncture_transport`); the three opens cover the stage
(`strictProductStage_cover`).

Hence `oldStrictDivisor j : CartierDivisor (projectiveContactStage k (j+2))` is an effective
Cartier divisor with regular equations whose ideal-sheaf data is `oldStrictIdeal j`, with
`cartierPicardHom (oldStrictDivisor j) = −[gluedKernelLine (oldStrictIdeal j)]`.

Not proved here: the identification of this class with lane A2's `oldStrictPicardClass j`
(`−[oldStrictKernelLine j]`), which needs `schemeKernelIdeal f ≅ schemeKernelIdeal f.ker.gluedTo`
for `f = oldExceptionalStrictι j` (private in the accepted modules); and the later stages
`N > j+2` (`oldFinalMap N j h`), whose puncture transport needs a pullback square over the
isomorphism locus that lane A2 records only at the module level (`oldLocusIso`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalBirthCartier

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusOldExceptionalChartIdeals
  FrobeniusOldExceptionalFirstChartFrame FrobeniusOldExceptionalSecondChartFrame
  FrobeniusOldExceptionalPuncture FrobeniusStrictTransformProductCover
  FrobeniusStrictTransformStepPuncture FrobeniusStrictTransformInvertible
  FrobeniusStrictTransformSecondChartFrame FrobeniusTowerFunctionField
  FrobeniusGraphPicardClassIntegral FrobeniusBlowupChartIteration FrobeniusExceptionalCartier
  FrobeniusFiberStrictCartier

variable {k : Type u} [Field k]

local instance initialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

local instance originMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The ideal sheaf of the strict transform `C_j` of `E_j` on its birth stage `j+2`. -/
abbrev oldStrictIdeal (j : ℕ) : (projectiveContactStage (k := k) (j + 1 + 1)).IdealSheafData :=
  (oldExceptionalStrictι (k := k) j).ker

/-- `C_j` misses the selected chart open of stage `j+2`. -/
theorem oldStrictIdeal_firstOpen (j : ℕ) :
    (oldStrictIdeal (k := k) j).ideal (firstAffineOpen (j + 1 + 1)) =
      Ideal.span
        {(1 : Γ(projectiveContactStage (k := k) (j + 1 + 1), (firstAffineOpen (j + 1 + 1)).1))} :=
  oldStrictIdeal_firstAffineOpen j

/-- On the second Rees open of stage `j+2`, `C_j` is cut out by the ratio coordinate. -/
theorem oldStrictIdeal_secondOpen (j : ℕ) :
    (oldStrictIdeal (k := k) j).ideal (secondAffineOpen (j + 1)) =
      Ideal.span {oldStrictSecondAmbientEquation j} :=
  oldStrictIdeal_secondAffineOpen j

/-- Over the centre complement of the last blowup, the ideal of `C_j` on stage `j+2` is the
transport of the ideal of `E_j` on stage `j+1` along the restricted blowdown. -/
theorem oldStrictIdeal_puncture_transport (j : ℕ)
    (W : (nextPuncture (k := k) (j + 1)).toScheme.affineOpens) :
    (oldStrictIdeal (k := k) j).ideal
        ⟨(nextPuncture (j + 1)).ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩ =
      ((stepExceptionalIdeal (k := k) j).ideal
          ⟨(currentPuncture (j + 1)).ι ''ᵁ (punctureIso (j + 1) ''ᵁ W.1),
            (W.2.image_of_isOpenImmersion (punctureIso (j + 1))).image_of_isOpenImmersion _⟩).comap
        ((punctureIso (j + 1)).appIso W.1).inv.hom := by
  rw [← Scheme.ker_morphismRestrict_ideal _ (nextPuncture (j + 1)) W,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _ (oldStrictOnPuncture_isPullback j) W]
  congr 1
  exact Scheme.ker_morphismRestrict_ideal
    (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
    (currentPuncture (j + 1)) ⟨punctureIso (j + 1) ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩

/-- A principal regular chart of the ideal of `E_j` on stage `j+1` containing the image of an
affine open `W` of the centre complement gives a principal regular generator of the ideal of `C_j`
on the image of `W`. -/
theorem oldStrictIdeal_puncture_chart (j : ℕ)
    (W : (nextPuncture (k := k) (j + 1)).toScheme.affineOpens) [Nonempty W.1]
    (c : PrincipalRegularChart (projectiveContactStage (k := k) (j + 1)) (stepExceptionalIdeal j))
    (hle : (currentPuncture (j + 1)).ι ''ᵁ (punctureIso (j + 1) ''ᵁ W.1) ≤ c.openSet.1) :
    (oldStrictIdeal (k := k) j).ideal
        ⟨(nextPuncture (j + 1)).ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩ =
      Ideal.span {((punctureIso (j + 1)).appIso W.1).hom
        ((projectiveContactStage (k := k) (j + 1)).presheaf.map (homOfLE hle).op c.generator)} ∧
    ((punctureIso (j + 1)).appIso W.1).hom
        ((projectiveContactStage (k := k) (j + 1)).presheaf.map (homOfLE hle).op c.generator) ∈
      nonZeroDivisors
        Γ(projectiveContactStage (k := k) (j + 1 + 1), (nextPuncture (j + 1)).ι ''ᵁ W.1) := by
  haveI : Nonempty ((currentPuncture (k := k) (j + 1)).ι ''ᵁ (punctureIso (j + 1) ''ᵁ W.1) :
      (projectiveContactStage (k := k) (j + 1)).Opens) := by
    obtain ⟨w⟩ := (inferInstance : Nonempty W.1)
    exact ⟨⟨(currentPuncture (j + 1)).ι.base ((punctureIso (j + 1)).base w.1),
      ⟨_, ⟨w.1, w.2, rfl⟩, rfl⟩⟩⟩
  have hspan := c.restrict_span_eq
    ⟨(currentPuncture (j + 1)).ι ''ᵁ (punctureIso (j + 1) ''ᵁ W.1),
      (W.2.image_of_isOpenImmersion (punctureIso (j + 1))).image_of_isOpenImmersion _⟩ hle
  have hreg := (c.restrict
    ⟨(currentPuncture (j + 1)).ι ''ᵁ (punctureIso (j + 1) ''ᵁ W.1),
      (W.2.image_of_isOpenImmersion (punctureIso (j + 1))).image_of_isOpenImmersion _⟩ hle).regular
  refine ⟨?_, regular_of_iso _ _ hreg⟩
  rw [oldStrictIdeal_puncture_transport j W, hspan]
  exact comap_inv_span ((punctureIso (j + 1)).appIso W.1) _

/-- The ideal sheaf of `C_j` on its birth stage is locally principal with regular generators. -/
theorem oldStrictIdeal_locallyPrincipalRegular (j : ℕ) :
    IdealLocallyPrincipalRegular (oldStrictIdeal (k := k) j) := by
  intro x
  rcases strictProductStage_cover (j + 1) x with hx | hx | hx
  · exact ⟨firstAffineOpen (j + 1 + 1), hx, 1, oldStrictIdeal_firstOpen j, Submonoid.one_mem _⟩
  · exact ⟨secondAffineOpen (j + 1), hx, _, oldStrictIdeal_secondOpen j,
      oldStrictSecondAmbientEquation_regular j⟩
  · obtain ⟨x', hx'⟩ : ∃ x' : (nextPuncture (k := k) (j + 1)).toScheme,
        (nextPuncture (j + 1)).ι.base x' = x := by
      have hr : x ∈ Set.range (nextPuncture (k := k) (j + 1)).ι.base := by
        rw [Scheme.Opens.range_ι]
        exact hx
      exact hr
    obtain ⟨U', hxU', d, hd, hdr⟩ := stepExceptionalIdeal_locallyPrincipalRegular j
      (((projectiveProductInitial (k := k)).stepProjection (j + 1)).base x)
    have hmem : x' ∈ punctureIso (j + 1) ⁻¹ᵁ ((currentPuncture (k := k) (j + 1)).ι ⁻¹ᵁ U'.1) := by
      change (currentPuncture (k := k) (j + 1)).ι.base ((punctureIso (j + 1)).base x') ∈ U'.1
      rw [← Scheme.comp_base_apply, morphismRestrict_ι, Scheme.comp_base_apply]
      change ((projectiveProductInitial (k := k)).stepProjection (j + 1)).base
        ((nextPuncture (j + 1)).ι.base x') ∈ U'.1
      rw [hx']
      exact hxU'
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
      (isBasis_affine_open (nextPuncture (k := k) (j + 1)).toScheme).exists_subset_of_mem_open hmem
        (punctureIso (j + 1) ⁻¹ᵁ ((currentPuncture (k := k) (j + 1)).ι ⁻¹ᵁ U'.1)).2
    haveI : Nonempty W := ⟨⟨x', hxW⟩⟩
    have hle : (currentPuncture (k := k) (j + 1)).ι ''ᵁ (punctureIso (j + 1) ''ᵁ W) ≤ U'.1 := by
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact hWle hz
    obtain ⟨hspan, hreg⟩ := oldStrictIdeal_puncture_chart j ⟨W, hW⟩
      ⟨U', ⟨⟨_, hxU'⟩⟩, d, hd, hdr⟩ hle
    exact ⟨⟨(nextPuncture (j + 1)).ι ''ᵁ W, hW.image_of_isOpenImmersion _⟩, ⟨x', hxW, hx'⟩, _,
      hspan, hreg⟩

/-- `C_j` as an effective Cartier divisor on its birth stage `j+2`. -/
def oldStrictDivisor (j : ℕ) : CartierDivisor (projectiveContactStage (k := k) (j + 1 + 1)) :=
  cartierDivisorOfIdeal _ (oldStrictIdeal j) (oldStrictIdeal_locallyPrincipalRegular j)

theorem oldStrictDivisor_hasRegularEquations (j : ℕ) :
    HasRegularCartierEquations (projectiveContactStage (k := k) (j + 1 + 1)) (oldStrictDivisor j) :=
  cartierDivisorOfIdeal_hasRegularEquations _ _ _

/-- The ideal-sheaf data of the divisor is the kernel of `oldExceptionalStrictι j`. -/
theorem oldStrictDivisor_idealData (j : ℕ) :
    effectiveCartierIdealDataOfRegularEquations (projectiveContactStage (k := k) (j + 1 + 1))
        (oldStrictDivisor j) (oldStrictDivisor_hasRegularEquations j) =
      oldStrictIdeal j :=
  cartierDivisorOfIdeal_idealData _ _ _

/-- The Cartier class of `C_j` is minus the class of the ideal line of its kernel. -/
theorem oldStrictDivisor_picard (j : ℕ) :
    cartierPicardHom (projectiveContactStage (k := k) (j + 1 + 1)) (oldStrictDivisor j) =
      -Additive.ofMul (gluedKernelLine (oldStrictIdeal j)
        (oldStrictIdeal_locallyPrincipalRegular j)).toPic :=
  cartierDivisorOfIdeal_picard _ _ _

end KltDP.Examples.FrobeniusOldExceptionalBirthCartier

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusOldExceptionalChartIdeals
  FrobeniusOldExceptionalBirthCartier FrobeniusTowerFunctionField
  FrobeniusGraphPicardClassIntegral

local instance birthInitialIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

/-- Bundle: on its birth stage `j+2`, the strict transform `C_j` of the exceptional curve `E_j` is
an effective Cartier divisor with regular equations whose ideal-sheaf data is the kernel of lane
A2's closed immersion `oldExceptionalStrictι j`, with Cartier class minus the class of that
kernel's ideal line. -/
theorem f29_old_exceptional_birth_cartier (k : Type u) [Field k] :
    ∀ j : ℕ,
      HasRegularCartierEquations (projectiveContactStage (k := k) (j + 1 + 1))
          (oldStrictDivisor j) ∧
      effectiveCartierIdealDataOfRegularEquations (projectiveContactStage (k := k) (j + 1 + 1))
          (oldStrictDivisor j) (oldStrictDivisor_hasRegularEquations j) =
        (oldExceptionalStrictι (k := k) j).ker ∧
      cartierPicardHom (projectiveContactStage (k := k) (j + 1 + 1)) (oldStrictDivisor j) =
        -Additive.ofMul (gluedKernelLine (oldStrictIdeal j)
          (oldStrictIdeal_locallyPrincipalRegular j)).toPic :=
  fun j => ⟨oldStrictDivisor_hasRegularEquations j, oldStrictDivisor_idealData j,
    oldStrictDivisor_picard j⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_old_exceptional_birth_cartier_universe_check (k : Type u) [Field k] : True := by
  have _ := f29_old_exceptional_birth_cartier.{u} k
  trivial

end KltDP.Examples
