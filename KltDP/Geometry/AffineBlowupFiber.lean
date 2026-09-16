import KltDP.Geometry.AffineBlowupConormal
import KltDP.Geometry.AffineBlowupCover
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Actual exceptional quotient charts in the scheme-theoretic center fiber

The fiber is the categorical pullback along the actual quotient `R → R/I`.
The chart comparison uses the pinned tensor-quotient equivalence and the
pinned affine scheme fiber-product isomorphism. Its two projections are
proved to be the actual quotient inclusion and quotient base map.
Pullback cancellation then identifies each local exceptional quotient
with an open subscheme of the whole fiber. No fiber presentation is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.AffineBlowup

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual closed center scheme and its quotient immersion into the base. -/
def centerInclusion : Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The scheme-theoretic inverse image of the actual center. -/
abbrev centerFiber := pullback (toSpec I) (centerInclusion I)

/-- The actual projection of the center fiber into the blowup. -/
abbrev centerFiberι : centerFiber I ⟶ scheme I :=
  pullback.fst (toSpec I) (centerInclusion I)

/-- The actual projection of the fiber to the center. -/
abbrev centerFiberToCenter : centerFiber I ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
  pullback.snd (toSpec I) (centerInclusion I)

variable (a : I)

/-- The tensor-product computation is applied to the actual chart base map. -/
def exceptionalChartFiberIso : exceptionalChart I a ≅
    pullback (Spec.map (CommRingCat.ofHom (chartBaseMap I a))) (centerInclusion I) := by
  letI := (chartBaseMap I a).toAlgebra
  exact (Scheme.Spec.mapIso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (chartRing I a) I).symm.toRingEquiv.toCommRingCatIso.op) ≪≫
        (pullbackSpecIso R (chartRing I a) (R ⧸ I)).symm

/-- The first projection of the comparison is the actual exceptional quotient inclusion. -/
@[reassoc] theorem exceptionalChartFiberIso_hom_fst :
    (exceptionalChartFiberIso I a).hom ≫ pullback.fst _ _ =
      exceptionalChartInclusion I a := by
  letI := (chartBaseMap I a).toAlgebra
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (chartRing I a) I
  change (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    (pullbackSpecIso R (chartRing I a) (R ⧸ I)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg (fun f : chartRing I a →+* exceptionalChartRing I a =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  change e.symm (x ⊗ₜ[R] (1 : R ⧸ I)) = Ideal.Quotient.mk (chartCenterIdeal I a) x
  simpa only [one_smul] using
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul (chartRing I a) I x 1

/-- The second projection is the actual map induced by killing the center ideal. -/
@[reassoc] theorem exceptionalChartFiberIso_hom_snd :
    (exceptionalChartFiberIso I a).hom ≫ pullback.snd _ _ =
      exceptionalChartToCenter I a := by
  letI := (chartBaseMap I a).toAlgebra
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (chartRing I a) I
  change (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    (pullbackSpecIso R (chartRing I a) (R ⧸ I)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  apply congrArg (fun f : (R ⧸ I) →+* exceptionalChartRing I a =>
    Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change e.symm ((1 : chartRing I a) ⊗ₜ[R] (Ideal.Quotient.mk I r)) =
    Ideal.Quotient.mk (chartCenterIdeal I a) (chartBaseMap I a r)
  simpa only [Algebra.smul_def, mul_one] using
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul (chartRing I a) I 1 r

/-- The local quotient chart is the actual pullback over the base center. -/
theorem exceptionalChart_isPullback :
    IsPullback (exceptionalChartInclusion I a) (exceptionalChartToCenter I a)
      (chartι I a ≫ toSpec I) (centerInclusion I) := by
  rw [chartι_toSpec I a]
  apply IsPullback.of_iso_pullback _ (exceptionalChartFiberIso I a)
    (exceptionalChartFiberIso_hom_fst I a) (exceptionalChartFiberIso_hom_snd I a)
  constructor
  change exceptionalChartInclusion I a ≫ Spec.map (CommRingCat.ofHom (chartBaseMap I a)) =
    exceptionalChartToCenter I a ≫ centerInclusion I
  have hchart : chartι I a ≫ toSpec I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := chartι_toSpec I a
  rw [← hchart, ← Category.assoc]
  exact (exceptionalChartToCenter_toSpec I a).symm

/-- The actual quotient chart's map into the full scheme-theoretic fiber. -/
def exceptionalChartToFiber : exceptionalChart I a ⟶ centerFiber I :=
  pullback.lift (exceptionalChartToBlowup I a) (exceptionalChartToCenter I a)
    (exceptionalChartToCenter_toSpec I a).symm

@[reassoc] theorem exceptionalChartToFiber_ι :
    exceptionalChartToFiber I a ≫ centerFiberι I = exceptionalChartToBlowup I a :=
  pullback.lift_fst _ _ _

@[reassoc] theorem exceptionalChartToFiber_toCenter :
    exceptionalChartToFiber I a ≫ centerFiberToCenter I = exceptionalChartToCenter I a :=
  pullback.lift_snd _ _ _

/-- Cancellation of actual pullback squares identifies the local quotient
with the inverse image of the ambient affine chart in the whole fiber. -/
theorem exceptionalChartToFiber_isPullback :
    IsPullback (exceptionalChartInclusion I a) (exceptionalChartToFiber I a)
      (chartι I a) (centerFiberι I) := by
  have h := exceptionalChart_isPullback I a
  rw [← exceptionalChartToFiber_toCenter I a] at h
  exact h.of_bot (exceptionalChartToFiber_ι I a).symm
    (IsPullback.of_hasPullback (toSpec I) (centerInclusion I))

/-- The quotient chart is an actual open subscheme of the fiber. -/
instance exceptionalChartToFiber_isOpenImmersion : IsOpenImmersion (exceptionalChartToFiber I a) := by
  rw [← (exceptionalChartToFiber_isPullback I a).flip.isoPullback_hom_fst]
  infer_instance

/-- The actual fiber restriction of the ambient affine chart has this quotient presentation. -/
def exceptionalChartRestrictionIso : exceptionalChart I a ≅
    pullback (centerFiberι I) (chartι I a) :=
  (exceptionalChartToFiber_isPullback I a).flip.isoPullback

@[reassoc] theorem exceptionalChartRestrictionIso_hom_fst :
    (exceptionalChartRestrictionIso I a).hom ≫ pullback.fst _ _ =
      exceptionalChartToFiber I a :=
  (exceptionalChartToFiber_isPullback I a).flip.isoPullback_hom_fst

/-- Any actual generating family of the center ideal supplies a cover of
its whole scheme-theoretic fiber by the corresponding quotient charts. -/
theorem exceptionalCharts_cover {ι : Type*} (f : ι → I)
    (hf : Ideal.span (Set.range (fun i => (f i : R))) = I) (x : centerFiber I) :
    ∃ i y, (exceptionalChartToFiber I (f i)).base y = x := by
  let 𝒰 := generatingAffineCover I f hf
  let 𝒱 := 𝒰.openCover.pullbackCover (centerFiberι I)
  obtain ⟨i, z, hz⟩ := 𝒱.exists_eq x
  let e : exceptionalChart I (f i) ≅ 𝒱.obj i := by
    change exceptionalChart I (f i) ≅ pullback (centerFiberι I) (𝒰.map i)
    rw [generatingAffineCover_map I f hf i]
    exact exceptionalChartRestrictionIso I (f i)
  have he : e.hom ≫ 𝒱.map i = exceptionalChartToFiber I (f i) := by
    change (exceptionalChartRestrictionIso I (f i)).hom ≫ pullback.fst _ _ = _
    exact exceptionalChartRestrictionIso_hom_fst I (f i)
  have hi : e.inv ≫ exceptionalChartToFiber I (f i) = 𝒱.map i := by
    rw [← he, Iso.inv_hom_id_assoc]
  refine ⟨i, e.inv.base z, ?_⟩
  have hb := congrArg (fun t : 𝒱.obj i ⟶ centerFiber I => t.base z) hi
  exact hb.trans hz

/-- The actual open cover by the exceptional quotient charts. -/
def exceptionalOpenCover {ι : Type*} (f : ι → I)
    (hf : Ideal.span (Set.range (fun i => (f i : R))) = I) :
    (centerFiber I).OpenCover :=
  Scheme.Cover.mkOfCovers ι (fun i => exceptionalChart I (f i))
    (fun i => exceptionalChartToFiber I (f i)) (exceptionalCharts_cover I f hf)

end KltDP.Geometry.AffineBlowup
