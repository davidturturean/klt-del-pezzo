import KltDP.Geometry.AffineBlowupFiber
import KltDP.Geometry.AffineBlowupExceptionalOverlap
import KltDP.Compatibility.SchemeTwoOpenCoverIso

/-!
# The actual intersection of exceptional quotient charts

The product-chart quotient is an actual open overlap of the exceptional
charts in the whole center fiber. Its image is computed from the actual
localization maps. The derived image equality and commuting square identify
it with the categorical pullback, using the existing open-immersion adapter.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.AffineBlowup

private theorem range_iso_comp {A B X : Scheme.{u}} (e : A ≅ B) (f : B ⟶ X) :
    Set.range (e.hom ≫ f).base = Set.range f.base := by
  rw [Scheme.comp_base, TopCat.coe_comp, Set.range_comp]
  have h : Function.Surjective e.hom.base := by
    rw [← TopCat.epi_iff_surjective]
    infer_instance
  rw [Set.range_eq_univ.mpr h, Set.image_univ]

private theorem range_of_isPullback {P A B X : Scheme.{u}}
    {s : P ⟶ A} {t : P ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    [IsOpenImmersion g] (h : IsPullback s t f g) :
    Set.range s.base = f.base ⁻¹' Set.range g.base := by
  rw [← h.isoPullback_hom_fst, range_iso_comp]
  exact IsOpenImmersion.range_pullback_fst_of_right g f

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

instance centerInclusion_isClosedImmersion : IsClosedImmersion (centerInclusion I) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective

instance centerFiberι_isClosedImmersion : IsClosedImmersion (centerFiberι I) := by
  exact MorphismProperty.pullback_fst (P := @IsClosedImmersion)
    (toSpec I) (centerInclusion I) (centerInclusion_isClosedImmersion I)

/-- The actual ambient product-chart restrictions commute in the blowup. -/
theorem conormalOverlap_morphism_condition :
    Spec.map (CommRingCat.ofHom (conormalOverlapLeft I a b)) ≫ chartι I a =
      Spec.map (CommRingCat.ofHom (conormalOverlapRight I a b)) ≫ chartι I b := by
  apply (cancel_epi (conormalOverlapIso I a b).hom).mp
  rw [← Category.assoc, conormalOverlapIso_hom_left,
    ← Category.assoc, conormalOverlapIso_hom_right, pullback.condition]

/-- The actual ambient product chart is the categorical chart intersection. -/
theorem conormalOverlap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (conormalOverlapLeft I a b)))
      (Spec.map (CommRingCat.ofHom (conormalOverlapRight I a b))) (chartι I a) (chartι I b) := by
  refine IsPullback.of_iso_pullback ⟨conormalOverlap_morphism_condition I a b⟩
    (conormalOverlapIso I a b).symm ?_ ?_
  · apply (cancel_epi (conormalOverlapIso I a b).hom).mp
    rw [Iso.symm_hom, Iso.hom_inv_id_assoc]
    exact (conormalOverlapIso_hom_left I a b).symm
  · apply (cancel_epi (conormalOverlapIso I a b).hom).mp
    rw [Iso.symm_hom, Iso.hom_inv_id_assoc]
    exact (conormalOverlapIso_hom_right I a b).symm

/-- The part of chart a also lying in chart b is the actual basic open at b/a. -/
theorem chart_preimage_chart_range :
    (chartι I a).base ⁻¹' Set.range (chartι I b).base =
      (PrimeSpectrum.basicOpen (chartFraction I a b)).carrier := by
  rw [← range_of_isPullback (conormalOverlap_isPullback I a b)]
  letI := (conormalOverlapLeft I a b).toAlgebra
  letI := conormalOverlapLeft_isLocalization I a b
  exact PrimeSpectrum.localization_away_comap_range (conormalOverlapRing I a b)
    (chartFraction I a b)

/-- The actual image of a quotient chart in the whole fiber. -/
theorem exceptionalChartToFiber_range :
    Set.range (exceptionalChartToFiber I a).base =
      (centerFiberι I).base ⁻¹' Set.range (chartι I a).base :=
  range_of_isPullback (exceptionalChartToFiber_isPullback I a).flip

/-- The actual exceptional quotient of the product chart, as an affine scheme. -/
def exceptionalOverlapScheme : Scheme := Spec (CommRingCat.of (exceptionalOverlapRing I a b))

def exceptionalOverlapLeftMorphism : exceptionalOverlapScheme I a b ⟶ exceptionalChart I a :=
  Spec.map (CommRingCat.ofHom (exceptionalOverlapLeft I a b))

def exceptionalOverlapRightMorphism : exceptionalOverlapScheme I a b ⟶ exceptionalChart I b :=
  Spec.map (CommRingCat.ofHom (exceptionalOverlapRight I a b))

instance exceptionalOverlapLeftMorphism_isOpenImmersion :
    IsOpenImmersion (exceptionalOverlapLeftMorphism I a b) := by
  letI := (exceptionalOverlapLeft I a b).toAlgebra
  letI := exceptionalOverlapLeft_isLocalization I a b
  exact IsOpenImmersion.of_isLocalization
    (Ideal.Quotient.mk (chartCenterIdeal I a) (chartFraction I a b))

instance exceptionalOverlapRightMorphism_isOpenImmersion :
    IsOpenImmersion (exceptionalOverlapRightMorphism I a b) := by
  letI := (exceptionalOverlapRight I a b).toAlgebra
  letI := exceptionalOverlapRight_isLocalization I a b
  exact IsOpenImmersion.of_isLocalization
    (Ideal.Quotient.mk (chartCenterIdeal I b) (chartFraction I b a))

@[reassoc] theorem exceptionalOverlapLeftMorphism_inclusion :
    exceptionalOverlapLeftMorphism I a b ≫ exceptionalChartInclusion I a =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (conormalOverlapIdeal I a b))) ≫
        Spec.map (CommRingCat.ofHom (conormalOverlapLeft I a b)) := by
  rw [exceptionalOverlapLeftMorphism, exceptionalChartInclusion,
    ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun f : chartRing I a →+* exceptionalOverlapRing I a b =>
    Spec.map (CommRingCat.ofHom f))
  exact Ideal.quotientMap_comp_mk (conormalOverlapLeft_ideal_le I a b)

@[reassoc] theorem exceptionalOverlapRightMorphism_inclusion :
    exceptionalOverlapRightMorphism I a b ≫ exceptionalChartInclusion I b =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (conormalOverlapIdeal I a b))) ≫
        Spec.map (CommRingCat.ofHom (conormalOverlapRight I a b)) := by
  rw [exceptionalOverlapRightMorphism, exceptionalChartInclusion,
    ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun f : chartRing I b →+* exceptionalOverlapRing I a b =>
    Spec.map (CommRingCat.ofHom f))
  exact Ideal.quotientMap_comp_mk (conormalOverlapRight_ideal_le I a b)

/-- The actual quotient restrictions commute in the whole scheme-theoretic fiber. -/
theorem exceptionalOverlap_morphism_condition :
    exceptionalOverlapLeftMorphism I a b ≫ exceptionalChartToFiber I a =
      exceptionalOverlapRightMorphism I a b ≫ exceptionalChartToFiber I b := by
  apply (cancel_mono (centerFiberι I)).mp
  rw [Category.assoc, exceptionalChartToFiber_ι,
    Category.assoc, exceptionalChartToFiber_ι]
  change exceptionalOverlapLeftMorphism I a b ≫ (exceptionalChartInclusion I a ≫ chartι I a) =
    exceptionalOverlapRightMorphism I a b ≫ (exceptionalChartInclusion I b ≫ chartι I b)
  let Q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (conormalOverlapIdeal I a b)))
  calc
    _ = (exceptionalOverlapLeftMorphism I a b ≫ exceptionalChartInclusion I a) ≫
        chartι I a := (Category.assoc _ _ _).symm
    _ = (Q ≫ Spec.map (CommRingCat.ofHom (conormalOverlapLeft I a b))) ≫ chartι I a :=
      congrArg (fun f => f ≫ chartι I a) (exceptionalOverlapLeftMorphism_inclusion I a b)
    _ = (Q ≫ Spec.map (CommRingCat.ofHom (conormalOverlapRight I a b))) ≫ chartι I b := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (fun f => Q ≫ f) (conormalOverlap_morphism_condition I a b)
    _ = (exceptionalOverlapRightMorphism I a b ≫ exceptionalChartInclusion I b) ≫
        chartι I b := congrArg (fun f => f ≫ chartι I b)
          (exceptionalOverlapRightMorphism_inclusion I a b).symm
    _ = _ := Category.assoc _ _ _

/-- The image of the product-chart quotient is exactly the overlap open in chart a. -/
theorem exceptionalOverlapLeftMorphism_range :
    Set.range (exceptionalOverlapLeftMorphism I a b).base =
      (exceptionalChartToFiber I a).base ⁻¹' Set.range (exceptionalChartToFiber I b).base := by
  rw [exceptionalChartToFiber_range]
  change Set.range (exceptionalOverlapLeftMorphism I a b).base =
    (exceptionalChartToFiber I a ≫ centerFiberι I).base ⁻¹' Set.range (chartι I b).base
  rw [exceptionalChartToFiber_ι]
  change Set.range (exceptionalOverlapLeftMorphism I a b).base =
    (exceptionalChartInclusion I a).base ⁻¹'
      ((chartι I a).base ⁻¹' Set.range (chartι I b).base)
  rw [chart_preimage_chart_range]
  letI := (exceptionalOverlapLeft I a b).toAlgebra
  letI := exceptionalOverlapLeft_isLocalization I a b
  have h := PrimeSpectrum.localization_away_comap_range (exceptionalOverlapRing I a b)
    (Ideal.Quotient.mk (chartCenterIdeal I a) (chartFraction I a b))
  exact h

/-- The actual quotient product chart is the scheme-theoretic intersection
of the two actual exceptional charts in the whole center fiber. -/
theorem exceptionalOverlap_isPullback :
    IsPullback (exceptionalOverlapLeftMorphism I a b) (exceptionalOverlapRightMorphism I a b)
      (exceptionalChartToFiber I a) (exceptionalChartToFiber I b) :=
  KltDP.SchemeTwoOpenGluing.isPullback_of_range
    (exceptionalOverlapLeftMorphism I a b) (exceptionalOverlapRightMorphism I a b)
    (exceptionalChartToFiber I a) (exceptionalChartToFiber I b)
    (exceptionalOverlap_morphism_condition I a b) (exceptionalOverlapLeftMorphism_range I a b)

end KltDP.Geometry.AffineBlowup
