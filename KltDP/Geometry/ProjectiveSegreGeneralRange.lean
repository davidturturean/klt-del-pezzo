import KltDP.Geometry.ProjectiveSegreGeneralMorphism
import KltDP.Geometry.ClosedImmersionOfChartSquares
import KltDP.Examples.FrobeniusProjectivePoints

/-!
# The Segre morphism is a closed immersion; products of projective schemes (DRAFT — untested)

* `mem_range_productChart_iff`: `x ∈ productChart i j ↔ fst x ∈ D(x_i) ∧ snd x ∈ D(y_j)` (pinned
  `Scheme.Pullback.range_map`);
* `range_productChart_eq_preimage`: **`range (productChart a b) = σ⁻¹(D(z_{ab}))`** for every Segre
  coordinate `w = z_{ab}` (a point of the chart `(i, j)` whose image has `z_{ab} ≠ 0` has
  `x_a/x_i ≠ 0` and `y_b/y_j ≠ 0`, hence lies in the chart `(a, b)`);
* `segreMorphism_isClosedImmersion` (chart squares over the coordinate charts of `P^{segreDim}`,
  pieces the product charts with the tuple normalised at the target coordinate);
* **`projectiveProductSpace_isProjective : IsProjectiveOverField (projectiveProductSpaceToSpec k m n)`**;
* **`isProjectiveOverField_pullback`**: the fibre product over `k` of two projective schemes over `k`
  is projective over `k` (closed immersion `pullback.map` into `P^m ×_k P^n`, pinned
  `MorphismProperty.pullback_map`, then Segre); the accepted `projectiveProduct k = P¹ ×_k P¹` is the
  case `m = n = 1` (`projectiveProduct_isProjectiveOverField_general`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.ProjectiveSegreGeneral

open KltDP.Geometry.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (m n : ℕ)

theorem mem_basicOpen_of_dvd' {R : Type u} [CommRing R] {a b : R} (h : a ∣ b) (q : PrimeSpectrum R)
    (hb : q ∈ PrimeSpectrum.basicOpen b) : q ∈ PrimeSpectrum.basicOpen a := by
  rw [PrimeSpectrum.mem_basicOpen] at hb ⊢
  obtain ⟨c, rfl⟩ := h
  exact fun ha => hb (Ideal.mul_mem_right c _ ha)

/-! ## Points of the product charts -/

/-- `x ∈ productChart i j ↔ fst x ∈ D(x_i) ∧ snd x ∈ D(y_j)`. -/
theorem mem_range_productChart_iff (i : Fin (m + 1)) (j : Fin (n + 1))
    (x : projectiveProductSpace k m n) :
    x ∈ Set.range (productChart k m n i j).base ↔
      (pullback.fst (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n)).base x ∈
          Set.range (coordinateChartMorphism k m i).base ∧
        (pullback.snd (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n)).base x ∈
          Set.range (coordinateChartMorphism k n j).base := by
  have e : Set.range (productChart k m n i j).base =
      Set.range ((productChartCover k m n).map (⟨i⟩, ⟨j⟩)).base := by
    rw [productChart]
    exact range_comp_base_of_isIso _ _
  rw [e]
  change x ∈ Set.range (pullback.map _ _ _ _ (coordinateChartMorphism k m i)
    (coordinateChartMorphism k n j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)).base ↔ _
  rw [Scheme.Pullback.range_map]
  exact Iff.rfl

/-- `σ (productChart i j q) ∈ D(z_w) ↔ segreTuple i j w ∉ q`. -/
theorem segre_mem_range_iff (i : Fin (m + 1)) (j : Fin (n + 1))
    (q : Spec (CommRingCat.of (productChartRing k m n i j))) (w : Fin (segreDim m n + 1)) :
    (segreMorphism k m n).base ((productChart k m n i j).base q) ∈
        Set.range (coordinateChartMorphism k (segreDim m n) w).base ↔
      q ∈ PrimeSpectrum.basicOpen (segreTuple k m n i j w) := by
  rw [← Scheme.comp_base_apply, productChart_segreMorphism]
  exact tupleMorphism_base_mem_range_iff _ _ _ _ _ q w

theorem segreIndex_fst_snd (w : Fin (segreDim m n + 1)) :
    segreIndex m n (segreEquiv m n w).1 (segreEquiv m n w).2 = w := by
  rw [segreIndex, Prod.mk.eta, Equiv.symm_apply_apply]

theorem segreTuple_at (w : Fin (segreDim m n + 1)) :
    segreTuple k m n (segreEquiv m n w).1 (segreEquiv m n w).2 w = 1 := by
  rw [segreTuple, chartFraction_self, chartFraction_self]
  rfl

/-- **The range identity**: `range (productChart a b) = σ⁻¹(D(z_{ab}))`. -/
theorem range_productChart_eq_preimage (w : Fin (segreDim m n + 1)) :
    Set.range (productChart k m n (segreEquiv m n w).1 (segreEquiv m n w).2).base =
      (segreMorphism k m n).base ⁻¹'
        Set.range (coordinateChartMorphism k (segreDim m n) w).base := by
  apply Set.Subset.antisymm
  · rintro x ⟨q, rfl⟩
    rw [Set.mem_preimage, segre_mem_range_iff, segreTuple_at, PrimeSpectrum.mem_basicOpen]
    exact fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · intro x hx
    obtain ⟨i, j, q, rfl⟩ := exists_productChart k m n x
    rw [Set.mem_preimage, segre_mem_range_iff] at hx
    rw [mem_range_productChart_iff]
    constructor
    · rw [← Scheme.comp_base_apply, productChart_fst, Scheme.comp_base_apply,
        coordinateChartMorphism_mem_range_iff, specMap_base_mem_basicOpen_iff]
      refine mem_basicOpen_of_dvd' ?_ q hx
      exact Dvd.intro ((1 : coordinateChartRing k m i) ⊗ₜ[k]
        chartFraction k n j (segreEquiv m n w).2) (tmul_eq_mul k _ _).symm
    · rw [← Scheme.comp_base_apply, productChart_snd, Scheme.comp_base_apply,
        coordinateChartMorphism_mem_range_iff, specMap_base_mem_basicOpen_iff]
      refine mem_basicOpen_of_dvd' ?_ q hx
      exact Dvd.intro (chartFraction k m i (segreEquiv m n w).1 ⊗ₜ[k]
        (1 : coordinateChartRing k n j)) (by rw [mul_comm]; exact (tmul_eq_mul k _ _).symm)

/-! ## The chart squares -/

/-- The Segre chart ring map normalised at any index equal to `z_{ij}` is surjective. -/
theorem segreChartHom_surjective_of (i : Fin (m + 1)) (j : Fin (n + 1))
    (w : Fin (segreDim m n + 1)) (hw : segreIndex m n i j = w) (h1 : segreTuple k m n i j w = 1) :
    Function.Surjective (tupleChartHom (segreDim m n) (algebraMap k (productChartRing k m n i j))
      (segreTuple k m n i j) w h1) := by
  subst hw
  exact segreChartHom_surjective k m n i j

/-- The piece over the coordinate chart `D(z_w)`, mapping into `Spec A_{(z_w)}`. -/
abbrev pieceSpec (w : Fin (segreDim m n + 1)) :
    Spec (CommRingCat.of (productChartRing k m n (segreEquiv m n w).1 (segreEquiv m n w).2)) ⟶
      Spec (CommRingCat.of (coordinateChartRing k (segreDim m n) w)) :=
  tupleSpec (segreDim m n) (algebraMap k _) (segreTuple k m n (segreEquiv m n w).1 (segreEquiv m n w).2)
    w (segreTuple_at k m n w)

instance pieceSpec_isClosedImmersion (w : Fin (segreDim m n + 1)) :
    IsClosedImmersion (pieceSpec k m n w) :=
  tupleSpec_isClosedImmersion _ _ _ _ _
    (segreChartHom_surjective_of k m n _ _ w (segreIndex_fst_snd m n w) (segreTuple_at k m n w))

theorem productChart_segreMorphism_piece (w : Fin (segreDim m n + 1)) :
    productChart k m n (segreEquiv m n w).1 (segreEquiv m n w).2 ≫ segreMorphism k m n =
      pieceSpec k m n w ≫ coordinateChartMorphism k (segreDim m n) w := by
  rw [productChart_segreMorphism]
  exact tupleMorphism_eq_of_scale _ _ _ _ _ _ _
    (fun z => by rw [segreTuple_at, one_mul])

/-- **The Segre morphism is a closed immersion.** -/
theorem segreMorphism_isClosedImmersion : IsClosedImmersion (segreMorphism k m n) :=
  isClosedImmersion_of_chartSquares (segreMorphism k m n) (coordinateChartCover k (segreDim m n))
    (fun w => Spec (CommRingCat.of
      (productChartRing k m n (segreEquiv m n w.down).1 (segreEquiv m n w.down).2)))
    (fun w => productChart k m n (segreEquiv m n w.down).1 (segreEquiv m n w.down).2)
    (fun w => pieceSpec k m n w.down)
    (fun w => productChart_segreMorphism_piece k m n w.down)
    (fun w => range_productChart_eq_preimage k m n w.down)

/-- **`P^m ×_k P^n` is projective over `k`.** -/
theorem projectiveProductSpace_isProjective :
    IsProjectiveOverField (projectiveProductSpaceToSpec k m n) :=
  ⟨segreDim m n, segreMorphism k m n, segreMorphism_isClosedImmersion k m n,
    segreMorphism_structure k m n⟩

/-! ## Products of projective schemes -/

/-- **The fibre product over `k` of two projective schemes over `k` is projective over `k`.** -/
theorem isProjectiveOverField_pullback {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (hf : IsProjectiveOverField f) (hg : IsProjectiveOverField g) :
    IsProjectiveOverField (pullback.fst f g ≫ f) := by
  obtain ⟨m, ι, hι, hιf⟩ := hf
  obtain ⟨n, κ, hκ, hκg⟩ := hg
  haveI : IsClosedImmersion (pullback.map f g (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n)
      ι κ (𝟙 _) ((Category.comp_id _).trans hιf.symm) ((Category.comp_id _).trans hκg.symm)) :=
    MorphismProperty.pullback_map (P := @IsClosedImmersion) hι hκ hιf.symm hκg.symm
  haveI : IsClosedImmersion (segreMorphism k m n) := segreMorphism_isClosedImmersion k m n
  refine ⟨segreDim m n, pullback.map f g (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n)
    ι κ (𝟙 _) ((Category.comp_id _).trans hιf.symm) ((Category.comp_id _).trans hκg.symm) ≫
      segreMorphism k m n, inferInstance, ?_⟩
  rw [Category.assoc, segreMorphism_structure, projectiveProductSpaceToSpec, ← Category.assoc,
    pullback.lift_fst, Category.assoc, hιf]

/-- The accepted `P¹ ×_k P¹` is the case `m = n = 1`. -/
theorem projectiveProduct_isProjectiveOverField_general :
    IsProjectiveOverField (KltDP.Examples.FrobeniusProjectivePoints.projectiveProductToSpec (k := k)) :=
  projectiveProductSpace_isProjective k 1 1

end KltDP.Geometry.ProjectiveSegreGeneral
