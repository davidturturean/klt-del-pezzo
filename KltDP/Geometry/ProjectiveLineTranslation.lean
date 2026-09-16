import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts
import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Geometry.ProjectiveSpaceIntegral
import KltDP.Examples.ProjectiveLinePointAtInfinity

/-!
# The translation automorphism `τ_c : P¹ ≅ P¹` over `k`

For `c : k` the graded ring automorphism `x₀ ↦ x₀`, `x₁ ↦ x₁ + c·x₀` of `k[x₀, x₁]`
(`translationHom c`) induces, on each homogeneous localization, the degree-zero map
`chartTranslationMap` (pinned `HomogeneousLocalization.map`), and the induced morphisms of the two
affine charts `D₊(x₀)`, `D₊(x₁ + c·x₀)` of the source (the pull-back of the standard cover) glue,
exactly as the accepted coordinate-power morphism `projectivePowerMorphism` does on the standard
cover, to the endomorphism `projectiveTranslation c` of the actual projective line
`projectiveSpace k 1`. It is over `k`, restricts on the finite polynomial chart to the accepted
translation `t ↦ t + c` (`parameterTranslationIso c`), sends the rational point `[1 : d]` to
`[1 : d + c]`, satisfies `τ_c ≫ τ_d = τ_{c+d}` and `τ_0 = 𝟙` (by the pinned
`ext_of_isDominant` on the dense finite chart), hence is an isomorphism with inverse `τ_{−c}`
(`projectiveTranslationIso c`), fixes the point at infinity, and in characteristic `p` commutes
with the coordinate-power morphism: `τ_c ≫ F_p = F_p ≫ τ_{c^p}`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveLineTranslation

open KltDP.Geometry ProjectiveChart ProjectiveLineComparison
open KltDP.Examples.FrobeniusProjectivePoints KltDP.Examples.FrobeniusTranslatedCharts
  KltDP.Examples.FrobeniusGlobalGraphCompatibility KltDP.Examples.FrobeniusGraphPicardClassPowerCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-! ## The graded translation of `k[x₀, x₁]` -/

/-- The images of the two homogeneous coordinates: `x₀ ↦ x₀`, `x₁ ↦ x₁ + c·x₀`. -/
def translationFamily (c : k) : Fin 2 → ProjectiveLineComparison.homogeneousRing k :=
  ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 0]

@[simp] theorem translationFamily_zero (c : k) :
    translationFamily c 0 = MvPolynomial.X 0 := rfl

@[simp] theorem translationFamily_one (c : k) :
    translationFamily c 1 = MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 0 := rfl

theorem translationFamily_isHomogeneous (c : k) (i : Fin 2) :
    (translationFamily c i).IsHomogeneous 1 := by
  fin_cases i
  · exact MvPolynomial.isHomogeneous_X k 0
  · have h := (MvPolynomial.isHomogeneous_C (Fin 2) c).mul (MvPolynomial.isHomogeneous_X k 0)
    rw [zero_add] at h
    exact (MvPolynomial.isHomogeneous_X k 1).add h

theorem translationFamily_mem (c : k) (i : Fin 2) : translationFamily c i ∈ ProjectiveLineComparison.grading k 1 :=
  translationFamily_isHomogeneous c i

/-- The graded translation `x₀ ↦ x₀`, `x₁ ↦ x₁ + c·x₀`, fixing the coefficients. -/
def translationHom (c : k) : ProjectiveLineComparison.homogeneousRing k →+* ProjectiveLineComparison.homogeneousRing k :=
  MvPolynomial.eval₂Hom MvPolynomial.C (translationFamily c)

@[simp] theorem translationHom_C (c r : k) :
    translationHom c (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [translationHom]

@[simp] theorem translationHom_X (c : k) (i : Fin 2) :
    translationHom c (MvPolynomial.X i) = translationFamily c i := by
  simp [translationHom]

theorem translationHom_X0 (c : k) : translationHom c (MvPolynomial.X 0) = MvPolynomial.X 0 :=
  translationHom_X c 0

theorem translationHom_X1 (c : k) :
    translationHom c (MvPolynomial.X 1) = MvPolynomial.X 1 + MvPolynomial.C c * MvPolynomial.X 0 :=
  translationHom_X c 1

/-- The translation preserves every homogeneous degree. -/
theorem translationHom_mem (c : k) (d : ℕ) (a : ProjectiveLineComparison.homogeneousRing k) (ha : a ∈ ProjectiveLineComparison.grading k d) :
    translationHom c a ∈ ProjectiveLineComparison.grading k d := by
  have h := (show a.IsHomogeneous d from ha).eval₂ MvPolynomial.C (translationFamily c)
    (fun r => MvPolynomial.isHomogeneous_C _ r) (translationFamily_isHomogeneous c)
  rw [one_mul] at h
  exact h

theorem translationHom_zero : translationHom (0 : k) = RingHom.id (ProjectiveLineComparison.homogeneousRing k) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i <;> simp [translationFamily]

theorem translationHom_comp (c d : k) :
    (translationHom d).comp (translationHom c) = translationHom (c + d) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i
    · simp [translationFamily]
    · simp [translationHom, translationFamily, MvPolynomial.C_add, add_mul, add_assoc, add_comm,
        add_left_comm]

/-! ## The induced maps of the homogeneous localizations -/

theorem powers_le_comap (c : k) (e e' : ProjectiveLineComparison.homogeneousRing k) (h : translationHom c e = e') :
    Submonoid.powers e ≤ (Submonoid.powers e').comap (translationHom c) := by
  rintro a ⟨m, rfl⟩
  exact ⟨m, by rw [map_pow, h]⟩

/-- The degree-zero map `A_{(e)} → A_{(e')}` induced by the translation, for `e' = τ(e)`. -/
def chartTranslationMap (c : k) (e e' : ProjectiveLineComparison.homogeneousRing k) (h : translationHom c e = e') :
    HomogeneousLocalization.Away (ProjectiveLineComparison.grading k) e →+* HomogeneousLocalization.Away (ProjectiveLineComparison.grading k) e' :=
  HomogeneousLocalization.map (ProjectiveLineComparison.grading k) (ProjectiveLineComparison.grading k) (translationHom c) (powers_le_comap c e e' h)
    (translationHom_mem c)

theorem chartTranslationMap_val (c : k) (e e' : ProjectiveLineComparison.homogeneousRing k) (h : translationHom c e = e')
    (x : HomogeneousLocalization.Away (ProjectiveLineComparison.grading k) e) :
    (chartTranslationMap c e e' h x).val =
      IsLocalization.map (Localization (Submonoid.powers e')) (translationHom c)
        (powers_le_comap c e e' h) x.val := by
  obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective x
  rw [chartTranslationMap, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk]
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk']

/-- The translation fixes the constants of every chart. -/
theorem chartTranslationMap_constants (c : k) (e e' : ProjectiveLineComparison.homogeneousRing k)
    (h : translationHom c e = e') (r : k) :
    chartTranslationMap c e e' h (KltDP.Examples.FrobeniusProjectiveMorphism.chartConstants e r) =
      KltDP.Examples.FrobeniusProjectiveMorphism.chartConstants e' r := by
  apply HomogeneousLocalization.val_injective
  rw [chartTranslationMap_val]
  change IsLocalization.map (Localization (Submonoid.powers e')) (translationHom c)
      (powers_le_comap c e e' h) (Localization.mk (MvPolynomial.C r) ⟨1, one_mem _⟩) =
    Localization.mk (MvPolynomial.C r) ⟨1, one_mem _⟩
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk', translationHom_C, map_one]

/-- The chart maps commute with the transition maps `A_{(e)} → A_{(e·g)}`. -/
theorem chartTranslationMap_awayMap (c : k) {e g x : ProjectiveLineComparison.homogeneousRing k} {d : ℕ}
    (hg : g ∈ ProjectiveLineComparison.grading k d) (hx : x = e * g) {e' g' x' : ProjectiveLineComparison.homogeneousRing k}
    (he' : translationHom c e = e') (hx' : translationHom c x = x')
    (hg'd : g' ∈ ProjectiveLineComparison.grading k d) (hx'' : x' = e' * g') :
    (HomogeneousLocalization.awayMap (ProjectiveLineComparison.grading k) hg'd hx'').comp (chartTranslationMap c e e' he') =
      (chartTranslationMap c x x' hx').comp (HomogeneousLocalization.awayMap (ProjectiveLineComparison.grading k) hg hx) := by
  let θ : Localization.Away e' →+* Localization.Away x' :=
    Localization.awayLift (algebraMap (ProjectiveLineComparison.homogeneousRing k) (Localization.Away x')) e'
      (isUnit_of_dvd_unit (map_dvd _ ⟨g', hx''⟩) (IsLocalization.Away.algebraMap_isUnit x'))
  let θ₀ : Localization.Away e →+* Localization.Away x :=
    Localization.awayLift (algebraMap (ProjectiveLineComparison.homogeneousRing k) (Localization.Away x)) e
      (isUnit_of_dvd_unit (map_dvd _ ⟨g, hx⟩) (IsLocalization.Away.algebraMap_isUnit x))
  have hθ : θ.comp (IsLocalization.map (Localization.Away e') (translationHom c)
      (powers_le_comap c e e' he')) =
      (IsLocalization.map (Localization.Away x') (translationHom c)
        (powers_le_comap c x x' hx')).comp θ₀ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers e)
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, IsLocalization.map_eq, θ, θ₀, Localization.awayLift,
      IsLocalization.Away.lift_eq]
  apply RingHom.ext
  intro z
  apply HomogeneousLocalization.val_injective
  simpa only [RingHom.comp_apply, HomogeneousLocalization.val_awayMap, chartTranslationMap_val, θ,
    θ₀] using RingHom.congr_fun hθ z.val

/-- The same compatibility after `Spec`, with the actual chart immersions of `Proj`. -/
theorem chartTranslationMorphism_overlap (c : k) {e g x : ProjectiveLineComparison.homogeneousRing k}
    (he : e ∈ ProjectiveLineComparison.grading k 1) (hg : g ∈ ProjectiveLineComparison.grading k 1) (hx : x = e * g)
    {e' g' x' : ProjectiveLineComparison.homogeneousRing k} (he' : translationHom c e = e') (hx' : translationHom c x = x')
    (hg'1 : g' ∈ ProjectiveLineComparison.grading k 1) (hx'' : x' = e' * g') :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (ProjectiveLineComparison.grading k) hg'1 hx'')) ≫
        (Spec.map (CommRingCat.ofHom (chartTranslationMap c e e' he')) ≫
          Proj.awayι (ProjectiveLineComparison.grading k) e he Nat.zero_lt_one) =
      Spec.map (CommRingCat.ofHom (chartTranslationMap c x x' hx')) ≫
        Proj.awayι (ProjectiveLineComparison.grading k) x (hx ▸ SetLike.mul_mem_graded he hg) (by decide) := by
  have h : CommRingCat.ofHom (chartTranslationMap c e e' he') ≫
      CommRingCat.ofHom (HomogeneousLocalization.awayMap (ProjectiveLineComparison.grading k) hg'1 hx'') =
      CommRingCat.ofHom (HomogeneousLocalization.awayMap (ProjectiveLineComparison.grading k) hg hx) ≫
        CommRingCat.ofHom (chartTranslationMap c x x' hx') :=
    CommRingCat.hom_ext (chartTranslationMap_awayMap c hg hx he' hx' hg'1 hx'')
  rw [← Category.assoc, ← Spec.map_comp, h, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]

/-! ## The pulled-back cover and the glued morphism -/

/-- `x₀` and `x₁ + c·x₀` generate the irrelevant ideal. -/
theorem irrelevant_le_span_translationFamily (c : k) :
    (HomogeneousIdeal.irrelevant (ProjectiveLineComparison.grading k)).toIdeal ≤ Ideal.span (Set.range (translationFamily c)) := by
  refine (irrelevant_le_span_coordinates k 1).trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Ideal.subset_span ⟨0, rfl⟩
  · have h1 : (MvPolynomial.X 1 : ProjectiveLineComparison.homogeneousRing k) =
        translationFamily c 1 - MvPolynomial.C c * translationFamily c 0 := by
      simp [translationFamily]
    change (MvPolynomial.X (1 : Fin 2) : ProjectiveLineComparison.homogeneousRing k) ∈ _
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.subset_span ⟨1, rfl⟩)
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩))

/-- The affine cover `D₊(x₀)`, `D₊(x₁ + c·x₀)` of the source. -/
def translationCover (c : k) : (projectiveSpace k 1).AffineOpenCover :=
  Proj.openCoverOfISupEqTop (ProjectiveLineComparison.grading k) (translationFamily c) (m := fun _ => 1)
    (translationFamily_mem c) (fun _ => Nat.zero_lt_one) (irrelevant_le_span_translationFamily c)

theorem translationCover_map (c : k) (i : Fin 2) :
    (translationCover c).map i =
      Proj.awayι (ProjectiveLineComparison.grading k) (translationFamily c i) (translationFamily_mem c i) Nat.zero_lt_one :=
  rfl

/-- The translation on the `i`-th piece of the pulled-back cover. -/
def localTranslation (c : k) (i : Fin 2) :
    (translationCover c).openCover.obj i ⟶ projectiveSpace k 1 :=
  Spec.map (CommRingCat.ofHom (chartTranslationMap c (MvPolynomial.X i) (translationFamily c i)
    (translationHom_X c i))) ≫ chartImmersion k i

theorem localTranslation_compatible (c : k) (i j : Fin 2) :
    pullback.fst ((translationCover c).map i) ((translationCover c).map j) ≫ localTranslation c i =
      pullback.snd ((translationCover c).map i) ((translationCover c).map j) ≫
        localTranslation c j := by
  let e := Proj.pullbackAwayιIso (ProjectiveLineComparison.grading k) (translationFamily_mem c i) Nat.zero_lt_one
    (translationFamily_mem c j) Nat.zero_lt_one
    (show translationFamily c i * translationFamily c j =
      translationFamily c i * translationFamily c j from rfl)
  have hx' : translationHom c (MvPolynomial.X i * MvPolynomial.X j) =
      translationFamily c i * translationFamily c j := by
    rw [map_mul, translationHom_X, translationHom_X]
  apply (cancel_epi e.inv).mp
  change e.inv ≫ (pullback.fst (Proj.awayι (ProjectiveLineComparison.grading k) (translationFamily c i)
      (translationFamily_mem c i) Nat.zero_lt_one)
      (Proj.awayι (ProjectiveLineComparison.grading k) (translationFamily c j) (translationFamily_mem c j) Nat.zero_lt_one) ≫
        (Spec.map (CommRingCat.ofHom (chartTranslationMap c (MvPolynomial.X i)
          (translationFamily c i) (translationHom_X c i))) ≫ chartImmersion k i)) =
    e.inv ≫ (pullback.snd (Proj.awayι (ProjectiveLineComparison.grading k) (translationFamily c i)
      (translationFamily_mem c i) Nat.zero_lt_one)
      (Proj.awayι (ProjectiveLineComparison.grading k) (translationFamily c j) (translationFamily_mem c j) Nat.zero_lt_one) ≫
        (Spec.map (CommRingCat.ofHom (chartTranslationMap c (MvPolynomial.X j)
          (translationFamily c j) (translationHom_X c j))) ≫ chartImmersion k j))
  rw [← Category.assoc e.inv, ← Category.assoc e.inv]
  rw [Proj.pullbackAwayιIso_inv_fst, Proj.pullbackAwayιIso_inv_snd]
  exact (chartTranslationMorphism_overlap c (MvPolynomial.isHomogeneous_X k i)
      (MvPolynomial.isHomogeneous_X k j) rfl (translationHom_X c i) hx'
      (translationFamily_mem c j) rfl).trans
    (chartTranslationMorphism_overlap c (MvPolynomial.isHomogeneous_X k j)
      (MvPolynomial.isHomogeneous_X k i) (mul_comm _ _) (translationHom_X c j) hx'
      (translationFamily_mem c i) (mul_comm _ _)).symm

/-- The pulled-back cover with indices lifted to the universe of the gluing API. -/
private def liftedTranslationCover (c : k) : Scheme.OpenCover.{u} (projectiveSpace k 1) where
  J := ULift.{u} (Fin 2)
  obj i := (translationCover c).openCover.obj i.down
  map i := (translationCover c).map i.down
  f x := ⟨(translationCover c).f x⟩
  covers x := (translationCover c).covers x

/-- **The translation `τ_c` of the projective line**, glued from the two chart maps. -/
def projectiveTranslation (c : k) : projectiveSpace k 1 ⟶ projectiveSpace k 1 :=
  (liftedTranslationCover c).glueMorphisms (fun i => localTranslation c i.down)
    (fun i j => localTranslation_compatible c i.down j.down)

theorem chart_projectiveTranslation (c : k) (i : Fin 2) :
    (translationCover c).map i ≫ projectiveTranslation c = localTranslation c i :=
  (liftedTranslationCover c).ι_glueMorphisms _ _ (ULift.up i)

/-- The chart map of the finite chart `D₊(x₀)`, which the translation preserves (its target
`translationFamily c 0` is `x₀` by definition). -/
def firstChartTranslationMap (c : k) :
    ProjectiveLineComparison.chartRing k 0 →+*
      HomogeneousLocalization.Away (ProjectiveLineComparison.grading k) (translationFamily c 0) :=
  chartTranslationMap c (MvPolynomial.X 0) (translationFamily c 0) (translationHom_X c 0)

/-- The first piece of the pulled-back cover is the finite chart. -/
theorem translationCover_map_zero (c : k) : (translationCover c).map (0 : Fin 2) = chartImmersion k 0 := rfl

/-- On the finite chart the translation is `Spec` of `firstChartTranslationMap`. -/
theorem chartImmersion_projectiveTranslation (c : k) :
    chartImmersion k 0 ≫ projectiveTranslation c =
      Spec.map (CommRingCat.ofHom (firstChartTranslationMap c)) ≫ chartImmersion k 0 := by
  -- elaborated without the expected type: with it, the chart index is unified before it is known
  have h := chart_projectiveTranslation c 0
  exact h

/-- `τ_c` is a morphism over `k`. -/
theorem projectiveTranslation_over_base (c : k) :
    projectiveTranslation c ≫ projectiveSpaceToSpec k 1 = projectiveSpaceToSpec k 1 := by
  apply (liftedTranslationCover c).hom_ext
  rintro ⟨i⟩
  change (translationCover c).map i ≫ (projectiveTranslation c ≫ projectiveSpaceToSpec k 1) =
    (translationCover c).map i ≫ projectiveSpaceToSpec k 1
  rw [← Category.assoc, chart_projectiveTranslation, localTranslation, translationCover_map]
  change (Spec.map (CommRingCat.ofHom (chartTranslationMap c (MvPolynomial.X i)
      (translationFamily c i) (translationHom_X c i))) ≫
        Proj.awayι (ProjectiveChart.grading k 1) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i)
          Nat.zero_lt_one) ≫ projectiveSpaceToSpec k 1 =
    Proj.awayι (ProjectiveChart.grading k 1) (translationFamily c i) (translationFamily_mem c i) Nat.zero_lt_one ≫
      projectiveSpaceToSpec k 1
  rw [Category.assoc, KltDP.Examples.FrobeniusProjectiveMorphism.awayι_over_base,
    KltDP.Examples.FrobeniusProjectiveMorphism.awayι_over_base, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact chartTranslationMap_constants c _ _ (translationHom_X c i) r

/-! ## The finite chart: `t ↦ t + c` -/

/-- Transport of a normalized fraction of the finite chart along the translation. -/
theorem firstChartTranslationMap_mk (c : k) (n : ℕ) (a : ProjectiveChart.homogeneousRing k 1)
    (ha : a ∈ ProjectiveChart.grading k 1 (n • 1)) :
    firstChartTranslationMap c
        (HomogeneousLocalization.Away.mk (ProjectiveChart.grading k 1)
          (MvPolynomial.isHomogeneous_X k (0 : Fin (1 + 1))) n a ha) =
      HomogeneousLocalization.Away.mk (ProjectiveChart.grading k 1)
        (MvPolynomial.isHomogeneous_X k (0 : Fin (1 + 1))) n (translationHom c a)
        (translationHom_mem c _ a ha) := by
  apply HomogeneousLocalization.val_injective
  unfold firstChartTranslationMap
  rw [chartTranslationMap_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk]
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  change translationHom c (MvPolynomial.X 0 ^ n) = MvPolynomial.X 0 ^ n
  rw [map_pow, translationHom_X0]

theorem translationHom_X_succ_zero (c : k) :
    translationHom c (MvPolynomial.X (Fin.succ (0 : Fin 1))) =
      MvPolynomial.X (Fin.succ (0 : Fin 1)) + MvPolynomial.C c * MvPolynomial.X 0 :=
  translationHom_X1 c

/-- Dehomogenized, the translation of the coordinate `x₁/x₀` is `t + c`. -/
theorem dehomogenize_firstChartTranslationMap_ratio (c : k) :
    dehomogenize k 1 (firstChartTranslationMap c (ratio k 1 0)) =
      MvPolynomial.X 0 + MvPolynomial.C c := by
  rw [ratio, firstChartTranslationMap_mk, dehomogenize_mk, translationHom_X_succ_zero, map_add,
    map_mul, dehomogenizePolynomial_X_succ, dehomogenizePolynomial_C,
    dehomogenizePolynomial_coordinate, mul_one]

theorem parameterTranslation_C (c r : k) :
    parameterTranslation c (Polynomial.C r) = Polynomial.C r := by
  simp [parameterTranslation]

theorem parameterTranslation_X (c : k) :
    parameterTranslation c Polynomial.X = Polynomial.X + Polynomial.C c := by
  simp [parameterTranslation]

/-- Through the polynomial identification of the finite chart, the translation is `t ↦ t + c`. -/
theorem chartPolynomialEquiv_translation (c : k) :
    (chartPolynomialEquiv k 0).toRingHom.comp (firstChartTranslationMap c) =
      (parameterTranslation c).toRingHom.comp (chartPolynomialEquiv k 0).toRingHom := by
  let e := chartPolynomialEquiv k 0
  have hc (r : k) : e.symm (Polynomial.C r) = chartConstants k 0 r := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (chartPolynomialEquiv_constants k 0 r).symm
  have hx : e.symm Polynomial.X = coordinate k 0 (otherIndex 0) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (chartPolynomialEquiv_otherCoordinate 0).symm
  have hf : (e.toRingHom.comp (firstChartTranslationMap c)).comp e.symm.toRingHom =
      (parameterTranslation c).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [hc]
      change e (firstChartTranslationMap c
        (KltDP.Examples.FrobeniusProjectiveMorphism.chartConstants (MvPolynomial.X 0) r)) = _
      unfold firstChartTranslationMap
      rw [chartTranslationMap_constants]
      exact (chartPolynomialEquiv_constants k 0 r).trans (parameterTranslation_C c r).symm
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [hx]
      change oneVariablePolynomialEquiv k
        (dehomogenize k 1 (firstChartTranslationMap c (ratio k 1 0))) = _
      rw [dehomogenize_firstChartTranslationMap_ratio, map_add, oneVariablePolynomialEquiv_X]
      change Polynomial.X + oneVariablePolynomialEquiv k (MvPolynomial.C c) =
        parameterTranslation c Polynomial.X
      rw [parameterTranslation_X, ← MvPolynomial.algebraMap_eq,
        (oneVariablePolynomialEquiv k).commutes, Polynomial.algebraMap_eq]
  apply RingHom.ext
  intro z
  have hz := RingHom.congr_fun hf (e z)
  change e (firstChartTranslationMap c (e.symm (e z))) = parameterTranslation c (e z) at hz
  rw [e.symm_apply_apply] at hz
  exact hz

/-- **On the finite polynomial chart the translation is the accepted `t ↦ t + c`.** -/
@[reassoc] theorem polynomialChartMap_projectiveTranslation (c : k) :
    polynomialChartMap k 0 ≫ projectiveTranslation c =
      (parameterTranslationIso c).hom ≫ polynomialChartMap k 0 := by
  change (Spec.map (CommRingCat.ofHom (chartPolynomialEquiv k 0).toRingHom) ≫ chartImmersion k 0) ≫
      projectiveTranslation c =
    Spec.map (CommRingCat.ofHom (parameterTranslation c).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (chartPolynomialEquiv k 0).toRingHom) ≫ chartImmersion k 0)
  rw [Category.assoc, chartImmersion_projectiveTranslation, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    chartPolynomialEquiv_translation]

/-! ## Points, composition, inverse -/

theorem coordinateEvaluation_comp_firstChartTranslationMap (c d : k) :
    (coordinateEvaluation d).comp (firstChartTranslationMap c) = coordinateEvaluation (d + c) := by
  have h : ((coordinateEvaluation d).comp (firstChartTranslationMap c)).comp
      (homogenizeRatios k 1) = (coordinateEvaluation (d + c)).comp (homogenizeRatios k 1) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, homogenizeRatios, MvPolynomial.eval₂Hom_C]
      rw [show constants k 1 r =
          KltDP.Examples.FrobeniusProjectiveMorphism.chartConstants (MvPolynomial.X 0) r from rfl,
        show firstChartTranslationMap c = chartTranslationMap c (MvPolynomial.X 0) (MvPolynomial.X 0)
          (translationHom_X0 c) from rfl, chartTranslationMap_constants]
      exact (coordinateEvaluation_constants d r).trans (coordinateEvaluation_constants (d + c) r).symm
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [RingHom.comp_apply, homogenizeRatios, MvPolynomial.eval₂Hom_X']
      rw [coordinateEvaluation_ratio]
      change parameterEvaluation d (dehomogenize k 1 (firstChartTranslationMap c (ratio k 1 0))) = d + c
      rw [dehomogenize_firstChartTranslationMap_ratio]
      simp [parameterEvaluation]
  apply RingHom.ext
  intro z
  have hz := RingHom.congr_fun h (dehomogenize k 1 z)
  simpa only [RingHom.comp_apply, homogenizeRatios_dehomogenize] using hz

/-- **`τ_c` sends the rational point `[1 : d]` to `[1 : d + c]`.** -/
theorem pointMorphism_projectiveTranslation (c d : k) :
    pointMorphism d ≫ projectiveTranslation c = pointMorphism (d + c) := by
  rw [pointMorphism, pointMorphism, Category.assoc]
  change Spec.map (CommRingCat.ofHom (coordinateEvaluation d)) ≫
      (chartImmersion k 0 ≫ projectiveTranslation c) =
    Spec.map (CommRingCat.ofHom (coordinateEvaluation (d + c))) ≫ chartImmersion k 0
  rw [chartImmersion_projectiveTranslation, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, coordinateEvaluation_comp_firstChartTranslationMap]

section Ext

local instance projectiveLine_isIntegral' : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance projectiveLine_isSeparated' : (projectiveSpace k 1).IsSeparated :=
  KltDP.Examples.FrobeniusGraphClosed.projectiveLine_isSeparated

/-- The finite chart is dense (`P¹` is irreducible). -/
local instance polynomialChartMap_isDominant : IsDominant (polynomialChartMap k 0) := by
  constructor
  apply (polynomialChartMap k 0).opensRange.isOpen.dense
  exact Set.range_nonempty _

theorem parameterTranslation_comp (c d : k) :
    (parameterTranslation d).toRingHom.comp (parameterTranslation c).toRingHom =
      (parameterTranslation (c + d)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change parameterTranslation d (parameterTranslation c (Polynomial.C r)) =
      parameterTranslation (c + d) (Polynomial.C r)
    rw [parameterTranslation_C, parameterTranslation_C, parameterTranslation_C]
  · change parameterTranslation d (parameterTranslation c Polynomial.X) =
      parameterTranslation (c + d) Polynomial.X
    rw [parameterTranslation_X, map_add, parameterTranslation_X, parameterTranslation_C,
      parameterTranslation_X, Polynomial.C_add]
    ring

theorem parameterTranslation_zero :
    (parameterTranslation (0 : k)).toRingHom = RingHom.id (Polynomial k) := by
  apply Polynomial.ringHom_ext
  · intro r
    change parameterTranslation (0 : k) (Polynomial.C r) = Polynomial.C r
    rw [parameterTranslation_C]
  · change parameterTranslation (0 : k) Polynomial.X = Polynomial.X
    rw [parameterTranslation_X, map_zero, add_zero]

/-- **`τ_c ≫ τ_d = τ_{c+d}`.** -/
theorem projectiveTranslation_comp (c d : k) :
    projectiveTranslation c ≫ projectiveTranslation d = projectiveTranslation (c + d) := by
  apply ext_of_isDominant (polynomialChartMap k 0)
  rw [← Category.assoc, polynomialChartMap_projectiveTranslation, Category.assoc,
    polynomialChartMap_projectiveTranslation, ← Category.assoc,
    polynomialChartMap_projectiveTranslation]
  congr 1
  change Spec.map (CommRingCat.ofHom (parameterTranslation c).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (parameterTranslation d).toRingHom) =
    Spec.map (CommRingCat.ofHom (parameterTranslation (c + d)).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, parameterTranslation_comp, add_comm]

/-- **`τ_0 = 𝟙`.** -/
theorem projectiveTranslation_zero : projectiveTranslation (0 : k) = 𝟙 (projectiveSpace k 1) := by
  apply ext_of_isDominant (polynomialChartMap k 0)
  rw [polynomialChartMap_projectiveTranslation, Category.comp_id]
  change Spec.map (CommRingCat.ofHom (parameterTranslation (0 : k)).toRingHom) ≫
    polynomialChartMap k 0 = polynomialChartMap k 0
  rw [parameterTranslation_zero]
  change Spec.map (𝟙 (CommRingCat.of (Polynomial k))) ≫ polynomialChartMap k 0 = _
  rw [Spec.map_id, Category.id_comp]

end Ext

theorem projectiveTranslation_neg_comp (c : k) :
    projectiveTranslation c ≫ projectiveTranslation (-c) = 𝟙 (projectiveSpace k 1) := by
  rw [projectiveTranslation_comp, add_neg_cancel, projectiveTranslation_zero]

theorem projectiveTranslation_comp_neg (c : k) :
    projectiveTranslation (-c) ≫ projectiveTranslation c = 𝟙 (projectiveSpace k 1) := by
  rw [projectiveTranslation_comp, neg_add_cancel, projectiveTranslation_zero]

/-- **The translation automorphism `τ_c : P¹ ≅ P¹`**, with inverse `τ_{−c}`. -/
def projectiveTranslationIso (c : k) : projectiveSpace k 1 ≅ projectiveSpace k 1 where
  hom := projectiveTranslation c
  inv := projectiveTranslation (-c)
  hom_inv_id := projectiveTranslation_neg_comp c
  inv_hom_id := projectiveTranslation_comp_neg c

instance projectiveTranslation_isIso (c : k) : IsIso (projectiveTranslation c) :=
  ⟨projectiveTranslation (-c), projectiveTranslation_neg_comp c, projectiveTranslation_comp_neg c⟩

/-! ## The point at infinity and the Frobenius power -/

/-- `τ_c` maps the finite chart into itself. -/
theorem projectiveTranslation_mem_chartOpen (c : k) (y : projectiveSpace k 1)
    (hy : y ∈ chartOpen k 0) : (projectiveTranslation c).base y ∈ chartOpen k 0 := by
  rw [← polynomialChartMap_opensRange] at hy ⊢
  obtain ⟨z, rfl⟩ := hy
  refine ⟨((parameterTranslationIso c).hom).base z, ?_⟩
  change ((parameterTranslationIso c).hom ≫ polynomialChartMap k 0).base z =
    (polynomialChartMap k 0 ≫ projectiveTranslation c).base z
  rw [polynomialChartMap_projectiveTranslation]

/-- **`τ_c` fixes the point at infinity.** -/
theorem projectiveTranslation_infinityPoint (c : k) :
    (projectiveTranslation c).base
      (KltDP.Examples.ProjectiveLinePointAtInfinity.infinityPoint (k := k)) =
      KltDP.Examples.ProjectiveLinePointAtInfinity.infinityPoint := by
  apply KltDP.Examples.ProjectiveLinePointAtInfinity.eq_infinityPoint_of_not_mem_chart
  intro h
  have h' := projectiveTranslation_mem_chartOpen (-c) _ h
  change ((projectiveTranslation c ≫ projectiveTranslation (-c)).base
    KltDP.Examples.ProjectiveLinePointAtInfinity.infinityPoint) ∈ chartOpen k 0 at h'
  rw [projectiveTranslation_neg_comp] at h'
  exact KltDP.Examples.ProjectiveLinePointAtInfinity.infinityPoint_not_mem_chart h'

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem parameterTranslation_polynomialPowerHom (c : k) :
    (parameterTranslation c).toRingHom.comp (polynomialPowerHom p) =
      (polynomialPowerHom p).comp (parameterTranslation (c ^ p)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change parameterTranslation c (polynomialPowerHom p (Polynomial.C r)) =
      polynomialPowerHom p (parameterTranslation (c ^ p) (Polynomial.C r))
    rw [polynomialPowerHom_C, parameterTranslation_C, parameterTranslation_C, polynomialPowerHom_C]
  · change parameterTranslation c (polynomialPowerHom p Polynomial.X) =
      polynomialPowerHom p (parameterTranslation (c ^ p) Polynomial.X)
    rw [polynomialPowerHom_X, map_pow, parameterTranslation_X, parameterTranslation_X, map_add,
      polynomialPowerHom_X, polynomialPowerHom_C, add_pow_char, ← Polynomial.C_pow]

local instance projectiveLine_isIntegral'' : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance projectiveLine_isSeparated'' : (projectiveSpace k 1).IsSeparated :=
  KltDP.Examples.FrobeniusGraphClosed.projectiveLine_isSeparated

local instance polynomialChartMap_isDominant' : IsDominant (polynomialChartMap k 0) := by
  constructor
  apply (polynomialChartMap k 0).opensRange.isOpen.dense
  exact Set.range_nonempty _

/-- **In characteristic `p` the translations commute with the coordinate-power morphism**:
`τ_c ≫ F_p = F_p ≫ τ_{c^p}` (`(t + c)^p = t^p + c^p`). -/
theorem projectiveTranslation_power (c : k) :
    projectiveTranslation c ≫
        KltDP.Examples.FrobeniusProjectiveMorphism.projectivePowerMorphism p =
      KltDP.Examples.FrobeniusProjectiveMorphism.projectivePowerMorphism p ≫
        projectiveTranslation (c ^ p) := by
  apply ext_of_isDominant (polynomialChartMap k 0)
  have h1 : polynomialChartMap k 0 ≫ (projectiveTranslation c ≫
      KltDP.Examples.FrobeniusProjectiveMorphism.projectivePowerMorphism p) =
      (parameterTranslationIso c).hom ≫ (Spec.map (CommRingCat.ofHom (polynomialPowerHom p)) ≫
        polynomialChartMap k 0) := by
    rw [← Category.assoc, polynomialChartMap_projectiveTranslation, Category.assoc,
      polynomialChartMap_power_both]
  have h2 : polynomialChartMap k 0 ≫
      (KltDP.Examples.FrobeniusProjectiveMorphism.projectivePowerMorphism p ≫
        projectiveTranslation (c ^ p)) =
      Spec.map (CommRingCat.ofHom (polynomialPowerHom p)) ≫
        ((parameterTranslationIso (c ^ p)).hom ≫ polynomialChartMap k 0) := by
    rw [← Category.assoc, polynomialChartMap_power_both, Category.assoc,
      polynomialChartMap_projectiveTranslation]
  rw [h1, h2, ← Category.assoc, ← Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom (parameterTranslation c).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (polynomialPowerHom p)) =
    Spec.map (CommRingCat.ofHom (polynomialPowerHom p)) ≫
      Spec.map (CommRingCat.ofHom (parameterTranslation (c ^ p)).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    parameterTranslation_polynomialPowerHom]

end Frobenius

end KltDP.Geometry.ProjectiveLineTranslation
