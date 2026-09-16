import KltDP.Geometry.QuadraticCoverTwoChart
import KltDP.Compatibility.SchemeTwoOpenCoverIso
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Finiteness of the constructed quadratic cover on two actual charts

The coefficient-restriction maps identify the quadratic overlap with the
inverse image of the base overlap. Joint surjectivity of the actual glued
charts then identifies each entire chart with the inverse image of its base
open. The resulting actual pullback squares transfer local finiteness to the
target cover. No preimage identification or finite covering morphism is an
input. This extends the already constructed two-chart cover; arbitrary atlas
descent and geometric branch properties remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverOpen

open TransitionUnitGluing QuadraticCover

private theorem range_precomp_iso {A B C : Scheme.{u}} (e : A ≅ B) (f : B ⟶ C) :
    Set.range (e.hom ≫ f).base = Set.range f.base := by
  rw [Scheme.comp_base, TopCat.coe_comp]
  exact Function.Surjective.range_comp (f := e.hom.base)
    (ConcreteCategory.bijective_of_isIso (C := TopCat) e.hom.base).surjective f.base

private theorem range_factor {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion g] :
    Set.range f.base = g.base ⁻¹' Set.range (f ≫ g).base := by
  rw [Scheme.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.preimage_image_eq _ g.isOpenEmbedding.injective]

/-- The actual coefficient-restriction chart has exactly the inverse-image
range of the smaller affine base open. -/
theorem range_restrictionMap (X : Scheme.{u}) {U W : X.Opens} (hWU : W ≤ U)
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (a : Γ(X, U)) :
    Set.range (restrictionMap X hWU a).base =
      (toBase a ≫ hU.fromSpec).base ⁻¹' (W : Set X) := by
  letI : Algebra Γ(X, U) Γ(X, W) := (res X hWU).toAlgebra
  have hspec : Set.range (Spec.map (CommRingCat.ofHom (res X hWU))).base =
      hU.fromSpec.base ⁻¹' (W : Set X) := by
    have h := range_factor (Spec.map (CommRingCat.ofHom (res X hWU))) hU.fromSpec
    have hcomp : Spec.map (CommRingCat.ofHom (res X hWU)) ≫ hU.fromSpec =
        hW.fromSpec := hU.map_fromSpec hW (homOfLE hWU).op
    rw [hcomp, IsAffineOpen.range_fromSpec] at h
    exact h
  change Set.range (baseChangeProjection (S := Γ(X, W)) a).base = _
  rw [← baseChangeSpecIso_inv_fst (S := Γ(X, W)) a]
  change Set.range ((baseChangeSpecIso Γ(X, W) a).symm.hom ≫
    pullback.fst (toBase a)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X, W))))).base = _
  rw [range_precomp_iso, Scheme.Pullback.range_fst]
  change (toBase a).base ⁻¹'
    Set.range (Spec.map (CommRingCat.ofHom (res X hWU))).base = _
  rw [hspec]
  rfl

/-- Precomposing the actual restriction by an isomorphism leaves its open range
unchanged. This includes the generator rescaling used on the right chart. -/
theorem range_iso_restrictionMap (X : Scheme.{u}) {U W : X.Opens} (hWU : W ≤ U)
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (a : Γ(X, U))
    {Z : Scheme.{u}} (e : Z ≅ affineScheme (res X hWU a)) :
    Set.range (e.hom ≫ restrictionMap X hWU a).base =
      (toBase a ≫ hU.fromSpec).base ⁻¹' (W : Set X) := by
  rw [range_precomp_iso, range_restrictionMap X hWU hU hW a]

end KltDP.Geometry.QuadraticCoverOpen

namespace KltDP.Geometry.QuadraticCoverTwoChart

open TransitionUnitGluing QuadraticCover QuadraticCoverOpen

namespace Data

variable {X : Scheme.{u}} (D : Data X)

private theorem leftToBase_mem (a : D.leftChart) : D.leftToBase.base a ∈ D.leftOpen := by
  have hmem : D.leftToBase.base a ∈ Set.range D.left_affine.fromSpec.base :=
    ⟨(toBase D.leftSection).base a, rfl⟩
  simpa only [IsAffineOpen.range_fromSpec] using hmem

private theorem rightToBase_mem (b : D.rightChart) : D.rightToBase.base b ∈ D.rightOpen := by
  have hmem : D.rightToBase.base b ∈ Set.range D.right_affine.fromSpec.base :=
    ⟨(toBase D.rightSection).base b, rfl⟩
  simpa only [IsAffineOpen.range_fromSpec] using hmem

/-- The left overlap is precisely the part of the left chart over the right base open. -/
theorem range_leftOverlap :
    Set.range D.leftOverlap.base = D.leftToBase.base ⁻¹' (D.rightOpen : Set X) := by
  have h := range_restrictionMap X
    (inf_le_left : D.leftOpen ⊓ D.rightOpen ≤ D.leftOpen)
    D.left_affine D.overlap_affine D.leftSection
  change Set.range D.leftOverlap.base =
    D.leftToBase.base ⁻¹' ((D.leftOpen ⊓ D.rightOpen : X.Opens) : Set X) at h
  rw [h]
  ext a
  exact ⟨fun h => h.2, fun h => ⟨D.leftToBase_mem a, h⟩⟩

/-- The inverse generator rescaling preserves the actual right overlap range. -/
theorem range_rightOverlap :
    Set.range D.rightOverlap.base = D.rightToBase.base ⁻¹' (D.leftOpen : Set X) := by
  have h := range_iso_restrictionMap X
    (inf_le_right : D.leftOpen ⊓ D.rightOpen ≤ D.rightOpen)
    D.right_affine D.overlap_affine D.rightSection
    (rescaleSpecIso
      (res X (inf_le_left : D.leftOpen ⊓ D.rightOpen ≤ D.leftOpen) D.leftSection)
      (res X (inf_le_right : D.leftOpen ⊓ D.rightOpen ≤ D.rightOpen) D.rightSection)
      D.transition D.branch_eq).symm
  change Set.range D.rightOverlap.base =
    D.rightToBase.base ⁻¹' ((D.leftOpen ⊓ D.rightOpen : X.Opens) : Set X) at h
  rw [h]
  ext b
  exact ⟨fun h => h.1, fun h => ⟨h, D.rightToBase_mem b⟩⟩

/-- The whole left chart is exactly the inverse image of its actual base open. -/
theorem range_leftι :
    Set.range D.leftι.base = D.morphism.base ⁻¹' (D.leftOpen : Set X) := by
  apply Set.Subset.antisymm
  · rintro y ⟨a, rfl⟩
    change (D.leftι ≫ D.morphism).base a ∈ D.leftOpen
    rw [D.leftι_morphism]
    exact D.leftToBase_mem a
  · intro y hy
    rcases D.jointly_surjective y with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨a, rfl⟩
    · have hb : b ∈ Set.range D.rightOverlap.base := by
        rw [D.range_rightOverlap]
        change (D.rightι ≫ D.morphism).base b ∈ D.leftOpen at hy
        rw [D.rightι_morphism] at hy
        exact hy
      obtain ⟨w, hw⟩ := hb
      refine ⟨D.leftOverlap.base w, ?_⟩
      change (D.leftOverlap ≫ D.leftι).base w = D.rightι.base b
      rw [D.overlapIsPullback.w]
      change D.rightι.base (D.rightOverlap.base w) = D.rightι.base b
      rw [hw]

/-- The whole right chart is exactly the inverse image of its actual base open. -/
theorem range_rightι :
    Set.range D.rightι.base = D.morphism.base ⁻¹' (D.rightOpen : Set X) := by
  apply Set.Subset.antisymm
  · rintro y ⟨b, rfl⟩
    change (D.rightι ≫ D.morphism).base b ∈ D.rightOpen
    rw [D.rightι_morphism]
    exact D.rightToBase_mem b
  · intro y hy
    rcases D.jointly_surjective y with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have ha : a ∈ Set.range D.leftOverlap.base := by
        rw [D.range_leftOverlap]
        change (D.leftι ≫ D.morphism).base a ∈ D.rightOpen at hy
        rw [D.leftι_morphism] at hy
        exact hy
      obtain ⟨w, hw⟩ := ha
      refine ⟨D.rightOverlap.base w, ?_⟩
      change (D.rightOverlap ≫ D.rightι).base w = D.leftι.base a
      rw [← D.overlapIsPullback.w]
      change D.leftι.base (D.leftOverlap.base w) = D.leftι.base a
      rw [hw]
    · exact ⟨b, rfl⟩

/-- Actual identification with the inverse-image open subscheme, retaining its inclusion. -/
def leftPreimageIso : D.leftChart ≅ (D.morphism ⁻¹ᵁ D.leftOpen).toScheme :=
  IsOpenImmersion.isoOfRangeEq D.leftι (D.morphism ⁻¹ᵁ D.leftOpen).ι
    (D.range_leftι.trans Subtype.range_coe.symm)

/-- The corresponding actual right chart identification. -/
def rightPreimageIso : D.rightChart ≅ (D.morphism ⁻¹ᵁ D.rightOpen).toScheme :=
  IsOpenImmersion.isoOfRangeEq D.rightι (D.morphism ⁻¹ᵁ D.rightOpen).ι
    (D.range_rightι.trans Subtype.range_coe.symm)

@[simp, reassoc]
theorem leftPreimageIso_hom_ι :
    D.leftPreimageIso.hom ≫ (D.morphism ⁻¹ᵁ D.leftOpen).ι = D.leftι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[simp, reassoc]
theorem rightPreimageIso_hom_ι :
    D.rightPreimageIso.hom ≫ (D.morphism ⁻¹ᵁ D.rightOpen).ι = D.rightι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The chart square is a pullback, derived from its proved inverse-image range. -/
def leftChartIsPullback :
    IsPullback D.leftι (toBase D.leftSection) D.morphism D.left_affine.fromSpec :=
  KltDP.SchemeTwoOpenGluing.isPullback_of_range
    D.leftι (toBase D.leftSection) D.morphism D.left_affine.fromSpec
    D.leftι_morphism
    (D.range_leftι.trans (congrArg (fun S : Set X => D.morphism.base ⁻¹' S)
      (IsAffineOpen.range_fromSpec D.left_affine).symm))

/-- The right chart square is also the actual base-change square. -/
def rightChartIsPullback :
    IsPullback D.rightι (toBase D.rightSection) D.morphism D.right_affine.fromSpec :=
  KltDP.SchemeTwoOpenGluing.isPullback_of_range
    D.rightι (toBase D.rightSection) D.morphism D.right_affine.fromSpec
    D.rightι_morphism
    (D.range_rightι.trans (congrArg (fun S : Set X => D.morphism.base ⁻¹' S)
      (IsAffineOpen.range_fromSpec D.right_affine).symm))

/-- The original two affine opens give an actual target open cover. -/
def baseChartCover : X.OpenCover :=
  KltDP.SchemeTwoOpenGluing.targetCover D.left_affine.fromSpec D.right_affine.fromSpec
    D.base_charts_cover

/-- Finiteness of the constructed structural morphism follows locally on its
actual target from the two proved quadratic-algebra base-change squares. -/
theorem morphism_isFinite : IsFinite D.morphism := by
  apply IsLocalAtTarget.of_openCover (P := @IsFinite) D.baseChartCover
  intro i
  cases i
  · change IsFinite (pullback.snd D.morphism D.left_affine.fromSpec)
    rw [← D.leftChartIsPullback.isoPullback_inv_snd]
    letI := toBase_isFinite D.leftSection
    infer_instance
  · change IsFinite (pullback.snd D.morphism D.right_affine.fromSpec)
    rw [← D.rightChartIsPullback.isoPullback_inv_snd]
    letI := toBase_isFinite D.rightSection
    infer_instance

end Data

export Data (range_leftOverlap range_rightOverlap range_leftι range_rightι
  leftPreimageIso rightPreimageIso leftPreimageIso_hom_ι leftPreimageIso_hom_ι_assoc
  rightPreimageIso_hom_ι rightPreimageIso_hom_ι_assoc leftChartIsPullback
  rightChartIsPullback baseChartCover morphism_isFinite)

end KltDP.Geometry.QuadraticCoverTwoChart
