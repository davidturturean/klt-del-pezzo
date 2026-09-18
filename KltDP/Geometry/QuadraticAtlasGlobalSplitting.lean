import KltDP.Geometry.QuadraticAtlasLocalSplitting
import KltDP.Geometry.QuadraticAtlasBaseIntersections

/-!
# Splitting the original globally glued quadratic cover

The original affine root equations construct the actual global splitting.
All three gluing compatibilities follow from the original atlas maps and
their proved actual intersections. The resulting isomorphism preserves
the original morphism to the base. No global split or component-count
statement is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.QuadraticAtlasGlobalSplitting

open TransitionUnitGluing QuadraticCover QuadraticCoverAtlas QuadraticAtlasLocalSplitting

variable {X : Scheme.{u}} {ι : Type u} (D : Data X ι)
    (a : ∀ i, Γ(X, D.opens i)ˣ)
    (ha : ∀ i, (a i : Γ(X, D.opens i)) ^ 2 = D.sections i)
    (hr : ∀ i j, res X (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
      (a i : Γ(X, D.opens i)) = (D.units i j : Γ(X, D.opens i ⊓ D.opens j)) *
        res X inf_le_right (a j : Γ(X, D.opens j)))
    (h2 : ∀ i, IsUnit (2 : Γ(X, D.opens i)))

def inclusion (ε : Bool) (Z : Scheme.{u}) : Z ⟶ Z ⨿ Z :=
  match ε with | false => coprod.inl | true => coprod.inr

@[reassoc]
theorem inclusion_map (ε : Bool) {Z T : Scheme.{u}} (q : Z ⟶ T) :
    inclusion ε Z ≫ coprod.map q q = q ≫ inclusion ε T := by
  cases ε <;> simp [inclusion]

def twoOn (h2 : ∀ i, IsUnit (2 : Γ(X, D.opens i))) {i : ι} {W : X.Opens} (hi : W ≤ D.opens i) : IsUnit (2 : Γ(X, W)) := by
  simpa only [map_ofNat] using (h2 i).map (res X hi)

def splitAt (i : ι) : D.chart i ≅ Spec Γ(X, D.opens i) ⨿ Spec Γ(X, D.opens i) :=
  splitOn D a ha (le_refl (D.opens i)) (h2 i)

def forwardAt (i : ι) : D.chart i ⟶ X ⨿ X :=
  forwardOn D a ha (le_refl (D.opens i)) (D.affine i) (h2 i)

include hr in
theorem forward_overlap (i j : ι) :
    D.overlapToChart i j ≫ forwardAt D a ha h2 i =
      (D.transition i j ≫ D.overlapToChart j i) ≫ forwardAt D a ha h2 j := by
  have hW := twoOn D h2 (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
  calc
    _ = forwardOn D a ha (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
        (D.pair_affine i j) hW :=
      map_forwardOn D a ha hr (le_refl _) inf_le_left inf_le_left
        (D.affine i) (D.pair_affine i j) (h2 i) hW
    _ = _ := by
      simp only [Data.transition, Data.overlapToChart, Data.map_comp]
      exact (map_forwardOn D a ha hr (le_refl (D.opens j))
        (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i) inf_le_right
        (D.affine j) (D.pair_affine i j) (h2 j) hW).symm

/-- The actual local splittings descend through the original scheme gluing. -/
def forward : D.scheme ⟶ X ⨿ X :=
  Multicoequalizer.desc D.glueData.toGlueData.diagram (X ⨿ X) (forwardAt D a ha h2)
    (by rintro ⟨i, j⟩; exact forward_overlap D a ha hr h2 i j)

@[simp, reassoc]
theorem chart_forward (i : ι) : D.chartι i ≫ forward D a ha hr h2 = forwardAt D a ha h2 i := by
  unfold forward Data.chartι
  apply Multicoequalizer.π_desc

def componentAt (ε : Bool) (i : ι) : Spec Γ(X, D.opens i) ⟶ D.scheme :=
  inclusion ε _ ≫ (splitAt D a ha h2 i).inv ≫ D.chartι i

/-- The original direct overlap map has the same original glued chart image. -/
theorem direct_overlap_chart (i j : ι) :
    D.map (le_refl (D.opens j)) (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
      inf_le_right ≫ D.chartι j = D.overlapToChart i j ≫ D.chartι i := by
  have h := D.glueData.glue_condition i j
  change D.transition i j ≫ D.overlapToChart j i ≫ D.chartι j =
    D.overlapToChart i j ≫ D.chartι i at h
  rw [← Category.assoc] at h
  simpa only [Data.transition, Data.overlapToChart, Data.map_comp] using h

include hr in
theorem component_overlap (ε : Bool) (i j : ι) :
    QuadraticAtlasBaseIntersections.left D i j ≫ componentAt D a ha h2 ε i =
      QuadraticAtlasBaseIntersections.right D i j ≫ componentAt D a ha h2 ε j := by
  have hW := twoOn D h2 (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
  let S := splitOn D a ha (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i) hW
  have hL := congrArg (fun z => inclusion ε (Spec Γ(X, D.opens i ⊓ D.opens j)) ≫ z ≫ D.chartι i)
    (splitOn_inv_map D a ha hr (le_refl (D.opens i))
      (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i) inf_le_left (h2 i) hW)
  have hR := congrArg (fun z => inclusion ε (Spec Γ(X, D.opens i ⊓ D.opens j)) ≫ z ≫ D.chartι j)
    (splitOn_inv_map D a ha hr (le_refl (D.opens j))
      (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i) inf_le_right (h2 j) hW)
  have hi : inclusion ε (Spec Γ(X, D.opens i ⊓ D.opens j)) ≫ S.inv ≫
      D.overlapToChart i j ≫ D.chartι i =
      QuadraticAtlasBaseIntersections.left D i j ≫ componentAt D a ha h2 ε i := by
    simpa only [S, splitAt, componentAt, Data.overlapToChart,
      QuadraticAtlasBaseIntersections.left, Category.assoc, inclusion_map_assoc] using hL
  have hj : inclusion ε (Spec Γ(X, D.opens i ⊓ D.opens j)) ≫ S.inv ≫
      D.overlapToChart i j ≫ D.chartι i =
      QuadraticAtlasBaseIntersections.right D i j ≫ componentAt D a ha h2 ε j := by
    simpa only [S, splitAt, componentAt, QuadraticAtlasBaseIntersections.right,
      Category.assoc, inclusion_map_assoc, direct_overlap_chart] using hR
  exact hi.symm.trans hj

include hr in
theorem component_compatible (ε : Bool) (i j : ι) :
    pullback.fst (D.baseCover.map i) (D.baseCover.map j) ≫ componentAt D a ha h2 ε i =
      pullback.snd _ _ ≫ componentAt D a ha h2 ε j := by
  change pullback.fst (D.affine i).fromSpec (D.affine j).fromSpec ≫ _ =
    pullback.snd _ _ ≫ _
  rw [← (QuadraticAtlasBaseIntersections.isPullback D i j).isoPullback_inv_fst,
    ← (QuadraticAtlasBaseIntersections.isPullback D i j).isoPullback_inv_snd,
    Category.assoc, Category.assoc, component_overlap D a ha hr h2 ε i j]

def component (ε : Bool) : X ⟶ D.scheme :=
  D.baseCover.glueMorphisms (componentAt D a ha h2 ε) (component_compatible D a ha hr h2 ε)

@[simp, reassoc]
theorem base_component (ε : Bool) (i : ι) :
    (D.affine i).fromSpec ≫ component D a ha hr h2 ε = componentAt D a ha h2 ε i :=
  D.baseCover.ι_glueMorphisms _ _ i

/-- The actual original quadratic cover splits over its original base. -/
def splitIso : D.scheme ≅ X ⨿ X where
  hom := forward D a ha hr h2
  inv := coprod.desc (component D a ha hr h2 false) (component D a ha hr h2 true)
  hom_inv_id := by
    apply D.glueData.openCover.hom_ext
    intro i
    change D.chartι i ≫ (forward D a ha hr h2 ≫ _) = D.chartι i ≫ 𝟙 _
    rw [← Category.assoc, chart_forward]
    have hc : coprod.desc (componentAt D a ha h2 false i) (componentAt D a ha h2 true i) =
        (splitAt D a ha h2 i).inv ≫ D.chartι i := by
      apply coprod.hom_ext <;> simp [componentAt, inclusion]
    simp only [forwardAt, forwardOn, Category.assoc, coprod.map_desc,
      base_component, hc, splitAt, Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply coprod.hom_ext
    · apply D.baseCover.hom_ext
      intro i
      change (D.affine i).fromSpec ≫
        (coprod.inl ≫ (coprod.desc _ _ ≫ forward D a ha hr h2)) =
          (D.affine i).fromSpec ≫ (coprod.inl ≫ 𝟙 _)
      simp only [coprod.inl_desc_assoc, Category.comp_id]
      rw [← Category.assoc, base_component]
      simp only [componentAt, inclusion, Category.assoc, chart_forward,
        forwardAt, forwardOn, splitAt, Iso.inv_hom_id_assoc, coprod.inl_map]
    · apply D.baseCover.hom_ext
      intro i
      change (D.affine i).fromSpec ≫
        (coprod.inr ≫ (coprod.desc _ _ ≫ forward D a ha hr h2)) =
          (D.affine i).fromSpec ≫ (coprod.inr ≫ 𝟙 _)
      simp only [coprod.inr_desc_assoc, Category.comp_id]
      rw [← Category.assoc, base_component]
      simp only [componentAt, inclusion, Category.assoc, chart_forward,
        forwardAt, forwardOn, splitAt, Iso.inv_hom_id_assoc, coprod.inr_map]

/-- The derived global splitting preserves the original cover morphism. -/
@[reassoc]
theorem splitIso_hom_fold :
    (splitIso D a ha hr h2).hom ≫ coprod.desc (𝟙 X) (𝟙 X) = D.morphism := by
  apply D.glueData.openCover.hom_ext
  intro i
  change D.chartι i ≫ (forward D a ha hr h2 ≫ _) = D.chartι i ≫ D.morphism
  rw [← Category.assoc, chart_forward, D.chartι_morphism]
  simp only [forwardAt, forwardOn, Category.assoc, coprod.map_desc, Category.comp_id]
  have hfold : coprod.desc (D.affine i).fromSpec (D.affine i).fromSpec =
      coprod.desc (𝟙 (Spec Γ(X, D.opens i))) (𝟙 (Spec Γ(X, D.opens i))) ≫
        (D.affine i).fromSpec := by
    apply coprod.hom_ext <;> simp
  rw [hfold, ← Category.assoc]
  exact congrArg (fun q => q ≫ (D.affine i).fromSpec)
    (QuadraticRootChartSplitting.hom_fold (res X (le_refl (D.opens i)) (D.sections i))
      (rootOn D a (le_refl (D.opens i))) (rootOn_sq D a ha (le_refl (D.opens i))) (h2 i))

end KltDP.Geometry.QuadraticAtlasGlobalSplitting

#print axioms KltDP.Geometry.QuadraticAtlasGlobalSplitting.splitIso
