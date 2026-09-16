import KltDP.Geometry.RationalTreePicardComponentPartition
import KltDP.Compatibility.QuotientIdealPullback

/-!
# Actual affine charts of the intersection of component unions

The pinned double-quotient equivalence turns the existing quotient
base-change square into the original sum-ideal square. Transport through
the actual component quotient charts identifies their affine pullback with
the spectrum of the quotient by the sum of their original ideals.

Both projections remain the original quotient morphisms. The resulting
map into the full scheme-theoretic intersection is an open immersion.
No nodality, reducedness of the intersection, or supplied chart
identification is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

section Quotient

variable (A : Type u) [CommRing A] (I J : Ideal A)

/-- The original quotient by the sum is the actual fiber product of the
two original quotient spectra. -/
theorem quotientSup_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left))))
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  let K : Ideal (A ⧸ I) := J.map (Ideal.Quotient.mk I)
  have h := KltDP.QuotientIdealPullback.isPullback (Ideal.Quotient.mk I) J K rfl
  let e : Spec (CommRingCat.of ((A ⧸ I) ⧸ K)) ≅
      Spec (CommRingCat.of (A ⧸ (I ⊔ J))) :=
    Scheme.Spec.mapIso (DoubleQuot.quotQuotEquivQuotSup I J).symm.toCommRingCatIso.op
  refine h.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom
        (DoubleQuot.quotQuotEquivQuotSup I J).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left)))
    rw [Category.comp_id, ← Spec.map_comp]
    apply congrArg (fun f : (A ⧸ I) →+* ((A ⧸ I) ⧸ K) =>
      Spec.map (CommRingCat.ofHom f))
    apply Ideal.Quotient.ringHom_ext
    rfl
  · change Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap K (Ideal.Quotient.mk I) Ideal.le_comap_map)) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom
        (DoubleQuot.quotQuotEquivQuotSup I J).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right)))
    rw [Category.comp_id, ← Spec.map_comp]
    apply congrArg (fun f : (A ⧸ J) →+* ((A ⧸ I) ⧸ K) =>
      Spec.map (CommRingCat.ofHom f))
    apply Ideal.Quotient.ringHom_ext
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end Quotient

variable (X : Scheme.{u}) [NoetherianSpace X]
  (S : Set ↥(irreducibleComponents X)) (U : X.affineOpens)

/-- The spectrum of the original affine sum-ideal quotient. -/
def componentIntersectionChart : Scheme.{u} :=
  Spec (CommRingCat.of (Γ(X, U.1) ⧸
    (componentChartIdeal X S U ⊔ componentChartIdeal X Sᶜ U)))

/-- Its original quotient projection to the selected component chart. -/
def componentIntersectionChartLeft : componentIntersectionChart X S U ⟶
    (componentUnionInclusion X S ⁻¹ᵁ U.1).toScheme :=
  let I := componentChartIdeal X S U
  let J := componentChartIdeal X Sᶜ U
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left))) ≫
      (componentUnionChartIso X S U).hom

/-- Its original quotient projection to the complementary component chart. -/
def componentIntersectionChartRight : componentIntersectionChart X S U ⟶
    (componentUnionInclusion X Sᶜ ⁻¹ᵁ U.1).toScheme :=
  let I := componentChartIdeal X S U
  let J := componentChartIdeal X Sᶜ U
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right))) ≫
      (componentUnionChartIso X Sᶜ U).hom

/-- The original component-chart projections form a pullback square over
the original affine open, by the already proved chart identifications. -/
theorem componentIntersectionChart_isPullback :
    IsPullback (componentIntersectionChartLeft X S U)
      (componentIntersectionChartRight X S U)
      (componentUnionInclusion X S ∣_ U.1)
      (componentUnionInclusion X Sᶜ ∣_ U.1) := by
  refine (quotientSup_isPullback Γ(X, U.1)
    (componentChartIdeal X S U) (componentChartIdeal X Sᶜ U)).of_iso
      (Iso.refl _) (componentUnionChartIso X S U)
      (componentUnionChartIso X Sᶜ U) U.2.isoSpec.symm ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, componentIntersectionChartLeft]
  · simp only [Iso.refl_hom, Category.id_comp, componentIntersectionChartRight]
  · exact (componentUnionChartIso_hom_restrict X S U).symm
  · exact (componentUnionChartIso_hom_restrict X Sᶜ U).symm

/-- The actual affine pullback is the spectrum of the original sum-ideal
quotient, without replacing either closed-union morphism. -/
def componentIntersectionChartIso : componentIntersectionChart X S U ≅
    pullback (componentUnionInclusion X S ∣_ U.1)
      (componentUnionInclusion X Sᶜ ∣_ U.1) :=
  (componentIntersectionChart_isPullback X S U).isoPullback

@[reassoc]
theorem componentIntersectionChartIso_hom_fst :
    (componentIntersectionChartIso X S U).hom ≫ pullback.fst _ _ =
      componentIntersectionChartLeft X S U :=
  (componentIntersectionChart_isPullback X S U).isoPullback_hom_fst

@[reassoc]
theorem componentIntersectionChartIso_hom_snd :
    (componentIntersectionChartIso X S U).hom ≫ pullback.snd _ _ =
      componentIntersectionChartRight X S U :=
  (componentIntersectionChart_isPullback X S U).isoPullback_hom_snd

/-- The same chart's map into the full original scheme-theoretic
intersection, using only the actual open inclusions. -/
def componentIntersectionChartToIntersection : componentIntersectionChart X S U ⟶
    pullback (componentUnionInclusion X S) (componentUnionInclusion X Sᶜ) :=
  (componentIntersectionChartIso X S U).hom ≫
    pullback.map (componentUnionInclusion X S ∣_ U.1)
      (componentUnionInclusion X Sᶜ ∣_ U.1)
      (componentUnionInclusion X S) (componentUnionInclusion X Sᶜ)
      (componentUnionInclusion X S ⁻¹ᵁ U.1).ι
      (componentUnionInclusion X Sᶜ ⁻¹ᵁ U.1).ι U.1.ι
      (morphismRestrict_ι (componentUnionInclusion X S) U.1)
      (morphismRestrict_ι (componentUnionInclusion X Sᶜ) U.1)

/-- This quotient spectrum is an actual open chart of the full
intersection, so future geometric properties can restrict along it. -/
instance componentIntersectionChartToIntersection_isOpenImmersion :
    IsOpenImmersion (componentIntersectionChartToIntersection X S U) := by
  unfold componentIntersectionChartToIntersection
  infer_instance

@[reassoc]
theorem componentIntersectionChartToIntersection_fst :
    componentIntersectionChartToIntersection X S U ≫ pullback.fst _ _ =
      componentIntersectionChartLeft X S U ≫
        (componentUnionInclusion X S ⁻¹ᵁ U.1).ι := by
  unfold componentIntersectionChartToIntersection
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
    componentIntersectionChartIso_hom_fst]

@[reassoc]
theorem componentIntersectionChartToIntersection_snd :
    componentIntersectionChartToIntersection X S U ≫ pullback.snd _ _ =
      componentIntersectionChartRight X S U ≫
        (componentUnionInclusion X Sᶜ ⁻¹ᵁ U.1).ι := by
  unfold componentIntersectionChartToIntersection
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
    componentIntersectionChartIso_hom_snd]

/-- The ambient map is the original sum quotient followed by the original
affine chart map. In particular, it preserves the map to X. -/
theorem componentIntersectionChartToIntersection_over :
    componentIntersectionChartToIntersection X S U ≫ pullback.fst _ _ ≫
      componentUnionInclusion X S =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (componentChartIdeal X S U ⊔ componentChartIdeal X Sᶜ U))) ≫ U.2.fromSpec := by
  rw [componentIntersectionChartToIntersection_fst_assoc, ← morphismRestrict_ι]
  unfold componentIntersectionChartLeft
  rw [Category.assoc, componentUnionChartIso_hom_over,
    ← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun f : Γ(X, U.1) →+*
      (Γ(X, U.1) ⧸ (componentChartIdeal X S U ⊔ componentChartIdeal X Sᶜ U)) =>
    Spec.map (CommRingCat.ofHom f) ≫ U.2.fromSpec)
  exact Ideal.Quotient.factor_comp_mk le_sup_left

end KltDP.Geometry.RationalTreePicard
