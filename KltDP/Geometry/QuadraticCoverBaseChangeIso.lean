import KltDP.Geometry.QuadraticCoverBaseChangeOverlap
import KltDP.Geometry.QuadraticCoverBaseChangeChartCover

/-!
# The actual glued base-change atlas is the original global pullback

The actual coefficient chart maps agree on overlaps and cover the original
pullback. Their original overlap is proved to be their actual intersection.
Descent in both directions constructs the isomorphism and proves that it
preserves the original second projection to the new base scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

variable {X Y : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)
  (f : Y ⟶ X) [Y.IsSeparated]

/-- The local original coefficient maps descend to the actual global pullback. -/
def baseChangeToPullback : (D.baseChangeAtlas f).scheme ⟶ pullback D.morphism f :=
  Multicoequalizer.desc (D.baseChangeAtlas f).glueData.toGlueData.diagram
    (pullback D.morphism f) (D.baseChangeChartInclusion f)
    (by rintro ⟨i, j⟩; exact D.baseChangeChartInclusion_overlap f i j)

@[simp, reassoc]
theorem chart_baseChangeToPullback (i : D.BaseChangeIndex f) :
    (D.baseChangeAtlas f).chartι i ≫ D.baseChangeToPullback f =
      D.baseChangeChartInclusion f i := by
  unfold chartι baseChangeToPullback
  apply Multicoequalizer.π_desc

/-- The original pair chart is precisely the intersection of the two pullback charts. -/
theorem baseChangeChartOverlapIsPullback (i j : D.BaseChangeIndex f) :
    IsPullback ((D.baseChangeAtlas f).overlapToChart i j)
      ((D.baseChangeAtlas f).transition i j ≫ (D.baseChangeAtlas f).overlapToChart j i)
      (D.baseChangeChartInclusion f i) (D.baseChangeChartInclusion f j) := by
  apply KltDP.SchemeTwoOpenGluing.isPullback_of_range
    ((D.baseChangeAtlas f).overlapToChart i j)
    ((D.baseChangeAtlas f).transition i j ≫ (D.baseChangeAtlas f).overlapToChart j i)
    (D.baseChangeChartInclusion f i) (D.baseChangeChartInclusion f j)
    (D.baseChangeChartInclusion_overlap f i j)
  rw [overlapToChart, (D.baseChangeAtlas f).range_map _ _ _
    ((D.baseChangeAtlas f).affine i) ((D.baseChangeAtlas f).pair_affine i j),
    range_baseChangeChartInclusion]
  ext x
  change ((D.baseChangeAtlas f).chartToBase i).base x ∈
      ((D.baseChangeAtlas f).opens i ⊓ (D.baseChangeAtlas f).opens j) ↔
    (pullback.snd D.morphism f).base ((D.baseChangeChartInclusion f i).base x) ∈
      (D.baseChangeAtlas f).opens j
  have hx : ((D.baseChangeAtlas f).chartToBase i).base x ∈ (D.baseChangeAtlas f).opens i :=
    (D.baseChangeAtlas f).frameToBase_mem le_rfl ((D.baseChangeAtlas f).affine i) x
  have he : (pullback.snd D.morphism f).base ((D.baseChangeChartInclusion f i).base x) =
      ((D.baseChangeAtlas f).chartToBase i).base x :=
    congrArg (fun q => q.base x) (D.baseChangeChartInclusion_snd f i)
  rw [he]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- The original gluing inclusions agree on the actual target-cover pullbacks. -/
theorem baseChangeInverse_compatible (i j : D.BaseChangeIndex f) :
    pullback.fst ((D.baseChangeCover f).map i) ((D.baseChangeCover f).map j) ≫
        (D.baseChangeAtlas f).chartι i =
      pullback.snd _ _ ≫ (D.baseChangeAtlas f).chartι j := by
  change pullback.fst (D.baseChangeChartInclusion f i) (D.baseChangeChartInclusion f j) ≫
      (D.baseChangeAtlas f).chartι i =
    pullback.snd (D.baseChangeChartInclusion f i) (D.baseChangeChartInclusion f j) ≫
      (D.baseChangeAtlas f).chartι j
  rw [← (D.baseChangeChartOverlapIsPullback f i j).isoPullback_inv_fst,
    ← (D.baseChangeChartOverlapIsPullback f i j).isoPullback_inv_snd, Category.assoc]
  have h := (D.baseChangeAtlas f).glueData.glue_condition i j
  change (D.baseChangeAtlas f).transition i j ≫
      (D.baseChangeAtlas f).overlapToChart j i ≫ (D.baseChangeAtlas f).chartι j =
    (D.baseChangeAtlas f).overlapToChart i j ≫ (D.baseChangeAtlas f).chartι i at h
  simpa only [Category.assoc] using
    congrArg (fun q => (D.baseChangeChartOverlapIsPullback f i j).isoPullback.inv ≫ q) h.symm

/-- The inverse comes from descent of the original gluing inclusions on the actual cover. -/
def baseChangeFromPullback : pullback D.morphism f ⟶ (D.baseChangeAtlas f).scheme :=
  (D.baseChangeCover f).glueMorphisms ((D.baseChangeAtlas f).chartι)
    (D.baseChangeInverse_compatible f)

@[simp, reassoc]
theorem chart_baseChangeFromPullback (i : D.BaseChangeIndex f) :
    D.baseChangeChartInclusion f i ≫ D.baseChangeFromPullback f =
      (D.baseChangeAtlas f).chartι i :=
  (D.baseChangeCover f).ι_glueMorphisms _ _ i

/-- The actual glued coefficient atlas is the original global base change. -/
def baseChangeIso : (D.baseChangeAtlas f).scheme ≅ pullback D.morphism f where
  hom := D.baseChangeToPullback f
  inv := D.baseChangeFromPullback f
  hom_inv_id := by
    apply (D.baseChangeAtlas f).glueData.openCover.hom_ext
    intro i
    change (D.baseChangeAtlas f).chartι i ≫
      (D.baseChangeToPullback f ≫ D.baseChangeFromPullback f) =
        (D.baseChangeAtlas f).chartι i ≫ 𝟙 _
    rw [← Category.assoc, chart_baseChangeToPullback,
      chart_baseChangeFromPullback, Category.comp_id]
  inv_hom_id := by
    apply (D.baseChangeCover f).hom_ext
    intro i
    change D.baseChangeChartInclusion f i ≫
      (D.baseChangeFromPullback f ≫ D.baseChangeToPullback f) =
        D.baseChangeChartInclusion f i ≫ 𝟙 _
    rw [← Category.assoc, chart_baseChangeFromPullback,
      chart_baseChangeToPullback, Category.comp_id]

/-- The global comparison preserves the original map to the new base. -/
@[simp, reassoc]
theorem baseChangeIso_hom_snd :
    (D.baseChangeIso f).hom ≫ pullback.snd D.morphism f = (D.baseChangeAtlas f).morphism := by
  apply (D.baseChangeAtlas f).morphism_unique
  intro i
  change (D.baseChangeAtlas f).chartι i ≫
    (D.baseChangeToPullback f ≫ pullback.snd D.morphism f) = _
  rw [← Category.assoc, chart_baseChangeToPullback, baseChangeChartInclusion_snd]

@[simp, reassoc]
theorem baseChangeIso_inv_morphism :
    (D.baseChangeIso f).inv ≫ (D.baseChangeAtlas f).morphism = pullback.snd D.morphism f := by
  rw [← baseChangeIso_hom_snd, Iso.inv_hom_id_assoc]

#print axioms baseChangeIso
#print axioms baseChangeIso_hom_snd

end KltDP.Geometry.QuadraticCoverAtlas.Data
