import KltDP.Geometry.QuadraticCoverAtlasIntersections

/-!
# The actual quadratic scheme glued from an arbitrary affine atlas

The constructed triple quadratic charts are transported through their proved
pullback isomorphisms to produce the triple maps required by `Scheme.GlueData`.
Their cocycle is the proved actual-chart cocycle. Pinned scheme gluing then
constructs the cover and its structural morphism. Each whole chart is proved
to be the inverse image of its base open, yielding global finiteness and
flatness from the actual local quadratic algebras.

The only input is `QuadraticCoverAtlas.Data`: literal opens, actual affine pair
and triple intersections, the base open cover, original units and their
cocycle, original sections and their branch equations. No glued scheme,
transition isomorphism, finite-cover condition or preimage identification is
an input. Extracting these branch sections from a global line-bundle square
and proving geometric branch properties remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The actual triple permutation transported to the actual pair-chart pullbacks. -/
def tripleTransition (i j k : ι) :
    pullback (D.overlapToChart i j) (D.overlapToChart i k) ⟶
      pullback (D.overlapToChart j k) (D.overlapToChart j i) :=
  (D.tripleIsPullback i j k).isoPullback.inv ≫ D.tripleCycle i j k ≫
    (D.tripleIsPullback j k i).isoPullback.hom

/-- The library's projection compatibility is derived from actual chart compatibility. -/
theorem tripleTransition_fac (i j k : ι) :
    D.tripleTransition i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ D.transition i j := by
  apply (cancel_epi (D.tripleIsPullback i j k).isoPullback.hom).mp
  simpa only [tripleTransition, Category.assoc, Iso.hom_inv_id_assoc,
    IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_fst_assoc] using
    D.tripleCycle_fac i j k

/-- Pullback transport preserves the already proved actual triple cocycle. -/
theorem tripleTransition_cocycle (i j k : ι) :
    D.tripleTransition i j k ≫ D.tripleTransition j k i ≫ D.tripleTransition k i j =
      𝟙 (pullback (D.overlapToChart i j) (D.overlapToChart i k)) := by
  apply (cancel_epi (D.tripleIsPullback i j k).isoPullback.hom).mp
  simp only [tripleTransition, Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun f : D.triple i j k ⟶ D.triple i j k =>
      f ≫ (D.tripleIsPullback i j k).isoPullback.hom) (D.tripleCycle_cocycle i j k)

/-- Actual scheme gluing data derived entirely from the original branch atlas. -/
def glueData : Scheme.GlueData.{u} where
  J := ι
  U := D.chart
  V := fun ij => D.overlap ij.1 ij.2
  f := D.overlapToChart
  f_id i := inferInstance
  t := D.transition
  t_id := D.transition_self
  t' := D.tripleTransition
  t_fac := D.tripleTransition_fac
  cocycle := D.tripleTransition_cocycle
  f_open i j := inferInstance

/-- The actual scheme obtained from these derived gluing data. -/
abbrev scheme : Scheme.{u} := D.glueData.glued

/-- The original quadratic chart maps into the constructed scheme. -/
def chartι (i : ι) : D.chart i ⟶ D.scheme := D.glueData.ι i

instance chartι_isOpenImmersion (i : ι) : IsOpenImmersion (D.chartι i) := by
  dsimp only [chartι]
  infer_instance

/-- Actual chart inclusions cover the constructed scheme. -/
theorem charts_cover (y : D.scheme) : ∃ i x, (D.chartι i).base x = y :=
  D.glueData.ι_jointly_surjective y

/-- The structural morphism is constructed by descent of the original base maps. -/
def morphism : D.scheme ⟶ X := by
  refine Multicoequalizer.desc D.glueData.toGlueData.diagram X D.chartToBase ?_
  rintro ⟨i, j⟩
  change D.overlapToChart i j ≫ D.chartToBase i =
    (D.transition i j ≫ D.overlapToChart j i) ≫ D.chartToBase j
  simp only [Category.assoc, overlapToChart_toBase, transition_toBase]

@[simp, reassoc]
theorem chartι_morphism (i : ι) : D.chartι i ≫ D.morphism = D.chartToBase i := by
  unfold chartι morphism
  apply Multicoequalizer.π_desc

/-- The constructed structural map is uniquely determined by the original chart maps. -/
theorem morphism_unique (f : D.scheme ⟶ X)
    (h : ∀ i, D.chartι i ≫ f = D.chartToBase i) : f = D.morphism := by
  apply D.glueData.openCover.hom_ext
  intro i
  exact (h i).trans (D.chartι_morphism i).symm

/-- The prescribed overlap is the actual scheme-theoretic intersection of the glued charts. -/
def chartOverlapIsPullback (i j : ι) :
    IsPullback (D.overlapToChart i j) (D.transition i j ≫ D.overlapToChart j i)
      (D.chartι i) (D.chartι j) :=
  IsPullback.of_isLimit (D.glueData.vPullbackConeIsLimit i j)

/-- Each entire chart is exactly the inverse image of its original base open.
This uses actual gluing coverage and the already proved overlap image ranges. -/
theorem range_chartι (i : ι) :
    Set.range (D.chartι i).base = D.morphism.base ⁻¹' (D.opens i : Set X) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    change (D.chartι i ≫ D.morphism).base x ∈ D.opens i
    rw [D.chartι_morphism]
    exact D.frameToBase_mem _ (D.affine i) x
  · intro y hy
    obtain ⟨j, x, rfl⟩ := D.charts_cover y
    have hxi : (D.chartToBase j).base x ∈ D.opens i := by
      change (D.chartι j ≫ D.morphism).base x ∈ D.opens i at hy
      rw [D.chartι_morphism] at hy
      exact hy
    have hxj := D.frameToBase_mem (le_refl (D.opens j)) (D.affine j) x
    have hx : x ∈ Set.range (D.overlapToChart j i).base := by
      rw [overlapToChart, D.range_map _ _ _ (D.affine j) (D.pair_affine j i)]
      exact ⟨hxj, hxi⟩
    obtain ⟨z, hz⟩ := hx
    refine ⟨(D.transition j i ≫ D.overlapToChart i j).base z, ?_⟩
    change ((D.transition j i ≫ D.overlapToChart i j) ≫ D.chartι i).base z =
      (D.chartι j).base x
    have hglue : (D.transition j i ≫ D.overlapToChart i j) ≫ D.chartι i =
        D.overlapToChart j i ≫ D.chartι j := by
      simpa only [Category.assoc] using D.glueData.glue_condition j i
    rw [hglue]
    change (D.chartι j).base ((D.overlapToChart j i).base z) = (D.chartι j).base x
    rw [hz]

/-- Canonical actual identification with the inverse-image open subscheme. -/
def chartPreimageIso (i : ι) : D.chart i ≅ (D.morphism ⁻¹ᵁ D.opens i).toScheme :=
  IsOpenImmersion.isoOfRangeEq (D.chartι i) (D.morphism ⁻¹ᵁ D.opens i).ι
    ((D.range_chartι i).trans Subtype.range_coe.symm)

@[simp, reassoc]
theorem chartPreimageIso_hom_ι (i : ι) :
    (D.chartPreimageIso i).hom ≫ (D.morphism ⁻¹ᵁ D.opens i).ι = D.chartι i :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The original quadratic chart is the actual pullback along its base-chart immersion. -/
def chartIsPullback (i : ι) :
    IsPullback (D.chartι i) (toBase (res X (le_refl (D.opens i)) (D.sections i)))
      D.morphism (D.affine i).fromSpec :=
  KltDP.SchemeTwoOpenGluing.isPullback_of_range _ _ _ _ (D.chartι_morphism i)
    ((D.range_chartι i).trans (congrArg (fun S : Set X => D.morphism.base ⁻¹' S)
      (IsAffineOpen.range_fromSpec (D.affine i)).symm))

/-- The original literal base open cover gives an actual affine target cover. -/
def baseCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers ι (fun i => Spec Γ(X, D.opens i))
    (fun i => (D.affine i).fromSpec) (by
      intro x
      have hx : x ∈ (⨆ i, D.opens i) := by rw [D.covers]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      have hr : x ∈ Set.range (D.affine i).fromSpec.base := by
        rw [IsAffineOpen.range_fromSpec]
        exact hi
      obtain ⟨z, hz⟩ := hr
      exact ⟨i, z, hz⟩)

/-- The actual globally constructed quadratic cover is finite. -/
theorem morphism_isFinite : IsFinite D.morphism := by
  apply IsLocalAtTarget.of_openCover (P := @IsFinite) D.baseCover
  intro i
  change IsFinite (pullback.snd D.morphism (D.affine i).fromSpec)
  rw [← (D.chartIsPullback i).isoPullback_inv_snd]
  letI := toBase_isFinite (res X (le_refl (D.opens i)) (D.sections i))
  infer_instance

/-- The actual globally constructed quadratic cover is flat. -/
theorem morphism_flat : AlgebraicGeometry.Flat D.morphism := by
  apply IsLocalAtSource.of_openCover (P := @AlgebraicGeometry.Flat) D.glueData.openCover
  intro i
  change AlgebraicGeometry.Flat (D.chartι i ≫ D.morphism)
  rw [D.chartι_morphism]
  letI := toBase_flat (res X (le_refl (D.opens i)) (D.sections i))
  change AlgebraicGeometry.Flat
    (toBase (res X (le_refl (D.opens i)) (D.sections i)) ≫ (D.affine i).fromSpec)
  infer_instance

end KltDP.Geometry.QuadraticCoverAtlas.Data
