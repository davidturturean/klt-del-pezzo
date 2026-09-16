import KltDP.Geometry.QuadraticRootAtlasIntersections
import KltDP.Geometry.QuadraticIntrinsicRamification
import KltDP.Geometry.QuadraticCoverAtlasGluing

/-!
# The actual globally glued quadratic ramification subscheme

The original root-zero frames, with their proved overlap and triple maps,
give literal `Scheme.GlueData`. Descent constructs their map into the
already constructed quadratic cover. Each whole root-zero chart is proved
to be its inverse image over the original cover chart; target locality
then proves that the descended map is a closed immersion.

When two is invertible, these actual charts are the intrinsic annihilator
quotients of the original relative Kähler modules. No global subscheme,
gluing data, immersion, preimage isomorphism or ideal compatibility is an
additional input. Global Cartier-divisor and curve-intersection statements
remain separate.

Reuse: pinned Scheme.GlueData, its actual open cover, and target-local
closed immersions. The exact pullback-transport pattern is the existing
QuadraticCoverAtlasGluing construction. No new gluing foundation is ported.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The actual triple-frame cycle transported to the required chosen pullbacks. -/
def rootZeroTripleTransition (i j k : ι) :
    pullback (D.rootZeroOverlapToChart i j) (D.rootZeroOverlapToChart i k) ⟶
      pullback (D.rootZeroOverlapToChart j k) (D.rootZeroOverlapToChart j i) :=
  (D.rootZeroTripleIsPullback i j k).isoPullback.inv ≫ D.rootZeroTripleCycle i j k ≫
    (D.rootZeroTripleIsPullback j k i).isoPullback.hom

theorem rootZeroTripleTransition_fac (i j k : ι) :
    D.rootZeroTripleTransition i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ D.rootZeroTransition i j := by
  apply (cancel_epi (D.rootZeroTripleIsPullback i j k).isoPullback.hom).mp
  simpa only [rootZeroTripleTransition, Category.assoc, Iso.hom_inv_id_assoc,
    IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_fst_assoc] using
    D.rootZeroTripleCycle_fac i j k

theorem rootZeroTripleTransition_cocycle (i j k : ι) :
    D.rootZeroTripleTransition i j k ≫ D.rootZeroTripleTransition j k i ≫
      D.rootZeroTripleTransition k i j =
        𝟙 (pullback (D.rootZeroOverlapToChart i j) (D.rootZeroOverlapToChart i k)) := by
  apply (cancel_epi (D.rootZeroTripleIsPullback i j k).isoPullback.hom).mp
  simp only [rootZeroTripleTransition, Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun f : D.rootZeroTriple i j k ⟶ D.rootZeroTriple i j k =>
      f ≫ (D.rootZeroTripleIsPullback i j k).isoPullback.hom)
      (D.rootZeroTripleCycle_cocycle i j k)

/-- All root-zero scheme gluing data are derived from the original quadratic atlas. -/
def rootZeroGlueData : Scheme.GlueData.{u} where
  J := ι
  U := D.rootZeroChart
  V := fun ij => D.rootZeroOverlap ij.1 ij.2
  f := D.rootZeroOverlapToChart
  f_id i := inferInstance
  t := D.rootZeroTransition
  t_id := D.rootZeroTransition_self
  t' := D.rootZeroTripleTransition
  t_fac := D.rootZeroTripleTransition_fac
  cocycle := D.rootZeroTripleTransition_cocycle
  f_open i j := inferInstance

/-- The actual root-zero scheme over the whole constructed quadratic cover. -/
abbrev rootZeroGlobalScheme : Scheme.{u} := D.rootZeroGlueData.glued

def rootZeroGlobalChartι (i : ι) : D.rootZeroChart i ⟶ D.rootZeroGlobalScheme :=
  D.rootZeroGlueData.ι i

instance rootZeroGlobalChartι_isOpenImmersion (i : ι) :
    IsOpenImmersion (D.rootZeroGlobalChartι i) := by
  dsimp only [rootZeroGlobalChartι]
  infer_instance

theorem rootZeroGlobalCharts_cover (y : D.rootZeroGlobalScheme) :
    ∃ i x, (D.rootZeroGlobalChartι i).base x = y :=
  D.rootZeroGlueData.ι_jointly_surjective y

/-- The original local closed inclusions descend into the original quadratic cover. -/
def rootZeroGlobalι : D.rootZeroGlobalScheme ⟶ D.scheme := by
  refine Multicoequalizer.desc D.rootZeroGlueData.toGlueData.diagram D.scheme
    (fun i => rootZeroι (res X (le_refl (D.opens i)) (D.sections i)) ≫ D.chartι i) ?_
  rintro ⟨i, j⟩
  change D.rootZeroOverlapToChart i j ≫ rootZeroι _ ≫ D.chartι i =
    (D.rootZeroTransition i j ≫ D.rootZeroOverlapToChart j i) ≫ rootZeroι _ ≫ D.chartι j
  simp only [rootZeroOverlapToChart, rootZeroTransition, Category.assoc,
    rootZeroFrameMap_ι_assoc, rootZeroFrameMap_ι]
  have hg := congrArg (fun f : D.overlap i j ⟶ D.scheme =>
    rootZeroι (res X (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
      (D.sections i)) ≫ f) (D.glueData.glue_condition i j).symm
  simpa only [Category.assoc, overlapToChart, transition] using hg

@[simp, reassoc]
theorem rootZeroGlobalChartι_globalι (i : ι) :
    D.rootZeroGlobalChartι i ≫ D.rootZeroGlobalι =
      rootZeroι (res X (le_refl (D.opens i)) (D.sections i)) ≫ D.chartι i := by
  unfold rootZeroGlobalChartι rootZeroGlobalι
  apply Multicoequalizer.π_desc

/-- Its original base map agrees with the original branch-chart map. -/
@[reassoc]
theorem rootZeroGlobalChartι_toBase (i : ι) :
    D.rootZeroGlobalChartι i ≫ (D.rootZeroGlobalι ≫ D.morphism) =
      D.rootZeroChartToBase i := by
  change D.rootZeroGlobalChartι i ≫ (D.rootZeroGlobalι ≫ D.morphism) =
    rootZeroι (res X (le_refl (D.opens i)) (D.sections i)) ≫ D.chartToBase i
  rw [← Category.assoc, rootZeroGlobalChartι_globalι, Category.assoc, chartι_morphism]

/-- Every whole glued root-zero chart is the inverse image of its original base open. -/
theorem range_rootZeroGlobalChartι (i : ι) :
    Set.range (D.rootZeroGlobalChartι i).base =
      (D.rootZeroGlobalι ≫ D.morphism).base ⁻¹' (D.opens i : Set X) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    change (D.rootZeroGlobalChartι i ≫ (D.rootZeroGlobalι ≫ D.morphism)).base x ∈ D.opens i
    rw [D.rootZeroGlobalChartι_toBase]
    exact D.rootZeroFrameToBase_mem _ (D.affine i) x
  · intro y hy
    obtain ⟨j, x, rfl⟩ := D.rootZeroGlobalCharts_cover y
    have hxi : (D.rootZeroChartToBase j).base x ∈ D.opens i := by
      change (D.rootZeroGlobalChartι j ≫ (D.rootZeroGlobalι ≫ D.morphism)).base x ∈
        D.opens i at hy
      rwa [D.rootZeroGlobalChartι_toBase] at hy
    have hxj := D.rootZeroFrameToBase_mem (le_refl (D.opens j)) (D.affine j) x
    have hx : x ∈ Set.range (D.rootZeroOverlapToChart j i).base := by
      rw [rootZeroOverlapToChart,
        D.range_rootZeroFrameMap _ _ _ (D.affine j) (D.pair_affine j i)]
      exact ⟨hxj, hxi⟩
    obtain ⟨z, hz⟩ := hx
    refine ⟨(D.rootZeroTransition j i ≫ D.rootZeroOverlapToChart i j).base z, ?_⟩
    change ((D.rootZeroTransition j i ≫ D.rootZeroOverlapToChart i j) ≫
        D.rootZeroGlobalChartι i).base z = (D.rootZeroGlobalChartι j).base x
    have hg : (D.rootZeroTransition j i ≫ D.rootZeroOverlapToChart i j) ≫
        D.rootZeroGlobalChartι i =
      D.rootZeroOverlapToChart j i ≫ D.rootZeroGlobalChartι j := by
      simpa only [Category.assoc] using D.rootZeroGlueData.glue_condition j i
    rw [hg]
    change (D.rootZeroGlobalChartι j).base ((D.rootZeroOverlapToChart j i).base z) = _
    rw [hz]

/-- The original chart closed immersion is the actual restriction of the descended map. -/
def rootZeroGlobalChartIsPullback (i : ι) :
    IsPullback (D.rootZeroGlobalChartι i)
      (rootZeroι (res X (le_refl (D.opens i)) (D.sections i)))
      D.rootZeroGlobalι (D.chartι i) :=
  KltDP.SchemeTwoOpenGluing.isPullback_of_range _ _ _ _
    (D.rootZeroGlobalChartι_globalι i) (by
      rw [D.range_rootZeroGlobalChartι, D.range_chartι]
      rfl)

/-- Target locality proves that the actual descended map is a closed immersion. -/
theorem rootZeroGlobalι_isClosedImmersion : IsClosedImmersion D.rootZeroGlobalι := by
  apply IsLocalAtTarget.of_openCover (P := @IsClosedImmersion) D.glueData.openCover
  intro i
  change IsClosedImmersion (pullback.snd D.rootZeroGlobalι (D.chartι i))
  rw [← (D.rootZeroGlobalChartIsPullback i).isoPullback_inv_snd]
  infer_instance

/-- Each intrinsic ramification quotient is an actual chart of the descended closed scheme. -/
def intrinsicRamificationChartIso (h2 : IsUnit (2 : Γ(X, ⊤))) (i : ι) :
    ramificationScheme (res X (le_refl (D.opens i)) (D.sections i)) ≅ D.rootZeroChart i :=
  ramificationIsoRoot _ (by
    simpa only [map_ofNat] using h2.map (res X (show D.opens i ≤ ⊤ from le_top)))

/-- These intrinsic charts retain their original inclusion into the original cover. -/
@[reassoc]
theorem intrinsicRamificationChartIso_globalι
    (h2 : IsUnit (2 : Γ(X, ⊤))) (i : ι) :
    (D.intrinsicRamificationChartIso h2 i).hom ≫ D.rootZeroGlobalChartι i ≫
        D.rootZeroGlobalι =
      ramificationι (res X (le_refl (D.opens i)) (D.sections i)) ≫ D.chartι i := by
  rw [D.rootZeroGlobalChartι_globalι]
  exact ramificationIsoRoot_hom_ι_assoc _ _ _

end KltDP.Geometry.QuadraticCoverAtlas.Data
