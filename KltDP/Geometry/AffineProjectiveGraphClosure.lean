import KltDP.Geometry.AffineFiniteTypeProjectiveChart
import KltDP.Geometry.ClosedOpenSchematicImage
import KltDP.Geometry.SchematicImageIntegral
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian

/-!
# Actual projective graph closure of an original integral affine scheme

The original finite-type structure morphism supplies a finite closed affine
embedding. The graph of the original map to X is closed in the corresponding
affine chart of P^n ×_k X, since the original X → Spec k is separated.
Its actual quotient-glued schematic image is integral and closed in that
projective bundle. The original affine source is open in this actual image,
and projection to the original X is proper and retains the original map.

Projectivity over X is expressed by the constructed closed embedding into
the original P^n ×_k X. No normality or smoothness of its boundary is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.AffineProjectiveGraphClosure

open ProjectiveChart

/-- An original integral affine scheme of finite type over k embeds openly
in an actual integral closed subscheme of P^n ×_k X, proper over X and with
the original map to X. Its ambient support is the closure of the original image. -/
theorem exists_projective_closure {k : Type u} [Field k]
    {W X : Scheme.{u}} [IsAffine W] [IsIntegral W]
    (σ : X ⟶ Spec (CommRingCat.of k)) [IsSeparated σ]
    (w : W ⟶ X) [LocallyOfFiniteType (w ≫ σ)] :
    ∃ (n : ℕ) (Z : Scheme.{u}) (j : W ⟶ Z)
        (i : Z ⟶ pullback (projectiveSpaceToSpec k n) σ),
      IsIntegral Z ∧ IsOpenImmersion j ∧ IsClosedImmersion i ∧
      IsProper (i ≫ pullback.snd (projectiveSpaceToSpec k n) σ) ∧
      j ≫ i ≫ pullback.snd (projectiveSpaceToSpec k n) σ = w ∧
      Set.range i.base = closure (Set.range (j ≫ i).base) := by
  obtain ⟨n, e, he, hbase⟩ :=
    AffineFiniteTypeProjectiveChart.exists_closed_chart (w ≫ σ)
  letI : IsClosedImmersion e := he
  letI : NoetherianSpace W :=
    noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec (w ≫ σ)
  let π := projectiveSpaceToSpec k n
  let a := chartMorphism k n
  letI : IsProper π := inferInstanceAs (IsProper (projectiveSpaceToSpec k n))
  letI : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion (chartMorphism k n))
  let g : W ⟶ pullback π σ :=
    pullback.lift (e ≫ a) w ((Category.assoc e a π).trans hbase)
  let f : pullback π σ ⟶ projectiveSpace k n := pullback.fst π σ
  letI : IsSeparated f :=
    MorphismProperty.pullback_fst (P := @IsSeparated) π σ inferInstance
  let l : pullback a f ⟶ pullback π σ := pullback.snd a f
  letI : IsOpenImmersion l := inferInstanceAs (IsOpenImmersion (pullback.snd a f))
  have hga : g ≫ f = e ≫ a := pullback.lift_fst _ _ _
  let c : W ⟶ pullback a f := pullback.lift e g hga.symm
  have hc₁ : c ≫ pullback.fst a f = e := pullback.lift_fst _ _ _
  have hc₂ : c ≫ l = g := pullback.lift_snd _ _ _
  letI : IsSeparated (pullback.fst a f) :=
    MorphismProperty.pullback_fst (P := @IsSeparated) a f inferInstance
  letI : IsClosedImmersion (c ≫ pullback.fst a f) := by
    rw [hc₁]
    infer_instance
  letI : IsClosedImmersion c := IsClosedImmersion.of_comp c (pullback.fst a f)
  letI : QuasiCompact g := quasiCompact_of_noetherianSpace_source _
  letI : QuasiCompact (c ≫ l) := quasiCompact_of_noetherianSpace_source _
  have hopen : IsOpenImmersion (SchematicImageGlued.toImage g) := by
    have h := ClosedOpenSchematicImage.toImage_isOpenImmersion c l
    rwa [hc₂] at h
  letI : IsProper (pullback.snd π σ) :=
    MorphismProperty.pullback_snd (P := @IsProper) π σ inferInstance
  refine ⟨n, SchematicImageGlued.image g, SchematicImageGlued.toImage g,
    SchematicImageGlued.inclusion g, SchematicImageIntegral.image_isIntegral g,
    hopen, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← Category.assoc, SchematicImageGlued.toImage_inclusion]
    exact pullback.lift_snd _ _ _
  · rw [SchematicImageGlued.toImage_inclusion]
    exact SchematicImageIntegral.range_inclusion g

end KltDP.Geometry.AffineProjectiveGraphClosure
