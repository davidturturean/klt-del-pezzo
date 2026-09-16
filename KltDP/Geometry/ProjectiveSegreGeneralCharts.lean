import KltDP.Geometry.ProjectiveSpaceChartFunctionsGeneral
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The Segre chart maps of `P^m ×_k P^n ⟶ P^{(m+1)(n+1)-1}` (DRAFT — untested, see the F09 record)

The product `P^m ×_k P^n = pullback (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n)` is covered
by the product charts `productChart i j : Spec (A_{(x_i)} ⊗[k] B_{(y_j)}) ⟶ P^m ×_k P^n` (pinned
`pullbackSpecIso` and `Scheme.Pullback.openCoverOfLeftRight` of the coordinate chart covers; the
chart rings are `k`-algebras through their constants, `chartAlgebra`). On the chart `(i, j)` the Segre
coordinates `z_{ab} = x_a y_b`, indexed by `segreEquiv : Fin (segreDim m n + 1) ≃ Fin (m+1) × Fin (n+1)`
with `segreDim m n + 1 = (m+1)(n+1)`, are the tuple `segreTuple i j z = (x_a/x_i) ⊗ (y_b/y_j)`,
normalised at `(i, j)`; `segreChart i j = tupleMorphism … : Spec (A ⊗ B) ⟶ P^{segreDim}` is over `k`
(`segreChart_structure`) and its chart ring map is surjective (`segreChartHom_surjective`: the two
inclusions `A → A ⊗ B`, `B → A ⊗ B` factor through it by `mk_eq_eval_chartFraction`), so
`segreChartSpec i j` is a closed immersion into the chart `D(z_{ij})`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.ProjectiveSegreGeneral

open KltDP.Geometry.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (m n : ℕ)

/-! ## The chart rings as `k`-algebras and the product charts -/

/-- The chart ring `A_{(x_i)}` as a `k`-algebra through its constants. -/
instance chartAlgebra (i : Fin (m + 1)) : Algebra k (coordinateChartRing k m i) :=
  (coordinateChartConstants k m i).toAlgebra

theorem chart_algebraMap (i : Fin (m + 1)) :
    algebraMap k (coordinateChartRing k m i) = coordinateChartConstants k m i := rfl

/-- `P^m ×_k P^n`. -/
abbrev projectiveProductSpace : Scheme.{u} :=
  pullback (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n)

/-- The structure map of `P^m ×_k P^n`. -/
abbrev projectiveProductSpaceToSpec : projectiveProductSpace k m n ⟶ Spec (CommRingCat.of k) :=
  pullback.fst (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n) ≫ projectiveSpaceToSpec k m

/-- The coordinate ring `A_{(x_i)} ⊗[k] B_{(y_j)}` of the product chart `(i, j)`. -/
abbrev productChartRing (i : Fin (m + 1)) (j : Fin (n + 1)) : Type u :=
  coordinateChartRing k m i ⊗[k] coordinateChartRing k n j

/-- The product cover of `P^m ×_k P^n` by the pullbacks of the coordinate charts (pinned). -/
abbrev productChartCover : Scheme.OpenCover.{u} (projectiveProductSpace k m n) :=
  Scheme.Pullback.openCoverOfLeftRight (coordinateChartCover k m) (coordinateChartCover k n)
    (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n)

/-- The identification of the product-cover piece `(i, j)` with `Spec (A ⊗[k] B)`. -/
def productPieceIso (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (productChartCover k m n).obj (⟨i⟩, ⟨j⟩) ≅
      Spec (CommRingCat.of (productChartRing k m n i j)) :=
  pullback.congrHom (coordinateChartMorphism_over_base k m i)
      (coordinateChartMorphism_over_base k n j) ≪≫
    pullbackSpecIso k (coordinateChartRing k m i) (coordinateChartRing k n j)

/-- **The product chart `(i, j)`** of `P^m ×_k P^n`. -/
def productChart (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (productChartRing k m n i j)) ⟶ projectiveProductSpace k m n :=
  (productPieceIso k m n i j).inv ≫ (productChartCover k m n).map (⟨i⟩, ⟨j⟩)

instance productChart_isOpenImmersion (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsOpenImmersion (productChart k m n i j) := by
  unfold productChart
  infer_instance

/-- The inclusion `A →+* A ⊗[k] B`. -/
abbrev leftInclusion (i : Fin (m + 1)) (j : Fin (n + 1)) :
    coordinateChartRing k m i →+* productChartRing k m n i j :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The inclusion `B →+* A ⊗[k] B`. -/
abbrev rightInclusion (i : Fin (m + 1)) (j : Fin (n + 1)) :
    coordinateChartRing k n j →+* productChartRing k m n i j :=
  (Algebra.TensorProduct.includeRight :
    coordinateChartRing k n j →ₐ[k] productChartRing k m n i j).toRingHom

theorem productPieceIso_inv_fst (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (productPieceIso k m n i j).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (leftInclusion k m n i j)) := by
  rw [productPieceIso, Iso.trans_inv, Category.assoc, pullback.congrHom_inv]
  erw [pullback.lift_fst]
  rw [Category.comp_id]
  exact pullbackSpecIso_inv_fst k _ _

theorem productPieceIso_inv_snd (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (productPieceIso k m n i j).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (rightInclusion k m n i j)) := by
  rw [productPieceIso, Iso.trans_inv, Category.assoc, pullback.congrHom_inv]
  erw [pullback.lift_snd]
  rw [Category.comp_id]
  exact pullbackSpecIso_inv_snd k _ _

/-- The first projection of a product chart. -/
theorem productChart_fst (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productChart k m n i j ≫ pullback.fst (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n) =
      Spec.map (CommRingCat.ofHom (leftInclusion k m n i j)) ≫ coordinateChartMorphism k m i := by
  rw [productChart, Category.assoc]
  change (productPieceIso k m n i j).inv ≫
    (pullback.map _ _ _ _ (coordinateChartMorphism k m i) (coordinateChartMorphism k n j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _) ≫ pullback.fst _ _) = _
  rw [pullback.lift_fst, ← Category.assoc, productPieceIso_inv_fst]

/-- The second projection of a product chart. -/
theorem productChart_snd (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productChart k m n i j ≫ pullback.snd (projectiveSpaceToSpec k m) (projectiveSpaceToSpec k n) =
      Spec.map (CommRingCat.ofHom (rightInclusion k m n i j)) ≫ coordinateChartMorphism k n j := by
  rw [productChart, Category.assoc]
  change (productPieceIso k m n i j).inv ≫
    (pullback.map _ _ _ _ (coordinateChartMorphism k m i) (coordinateChartMorphism k n j) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _) ≫ pullback.snd _ _) = _
  rw [pullback.lift_snd, ← Category.assoc, productPieceIso_inv_snd]

theorem leftInclusion_comp_constants (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (leftInclusion k m n i j).comp (coordinateChartConstants k m i) =
      algebraMap k (productChartRing k m n i j) :=
  RingHom.ext fun _ => rfl

theorem rightInclusion_comp_constants (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (rightInclusion k m n i j).comp (coordinateChartConstants k n j) =
      algebraMap k (productChartRing k m n i j) :=
  RingHom.ext fun r => (Algebra.TensorProduct.algebraMap_apply' r).symm

/-- Every product chart is over `k`. -/
theorem productChart_toSpec (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productChart k m n i j ≫ projectiveProductSpaceToSpec k m n =
      Spec.map (CommRingCat.ofHom (algebraMap k (productChartRing k m n i j))) := by
  rw [projectiveProductSpaceToSpec, ← Category.assoc, productChart_fst, Category.assoc,
    coordinateChartMorphism_over_base, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    leftInclusion_comp_constants]

/-- Every point of the product lies in a product chart. -/
theorem exists_productChart (x : projectiveProductSpace k m n) :
    ∃ (i : Fin (m + 1)) (j : Fin (n + 1)), x ∈ Set.range (productChart k m n i j).base := by
  obtain ⟨y, hy⟩ := (productChartCover k m n).covers x
  refine ⟨((productChartCover k m n).f x).1.down, ((productChartCover k m n).f x).2.down,
    (productPieceIso k m n _ _).hom.base y, ?_⟩
  rw [productChart, Scheme.comp_base_apply,
    ← Scheme.comp_base_apply (productPieceIso k m n _ _).hom (productPieceIso k m n _ _).inv,
    Iso.hom_inv_id]
  exact hy

/-! ## The Segre index and tuple -/

/-- `segreDim m n + 1 = (m+1)(n+1)`. -/
abbrev segreDim : ℕ := m + n + m * n

theorem segreDim_succ : segreDim m n + 1 = (m + 1) * (n + 1) := by
  unfold segreDim
  ring

/-- The Segre coordinates indexed by pairs. -/
def segreEquiv : Fin (segreDim m n + 1) ≃ Fin (m + 1) × Fin (n + 1) :=
  (finCongr (segreDim_succ m n)).trans finProdFinEquiv.symm

/-- The Segre index of the product chart `(i, j)`. -/
abbrev segreIndex (i : Fin (m + 1)) (j : Fin (n + 1)) : Fin (segreDim m n + 1) :=
  (segreEquiv m n).symm (i, j)

theorem segreEquiv_segreIndex (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreEquiv m n (segreIndex m n i j) = (i, j) :=
  (segreEquiv m n).apply_symm_apply (i, j)

theorem chartFraction_self (N : ℕ) (i : Fin (N + 1)) : chartFraction k N i i = 1 := by
  rw [HomogeneousLocalization.ext_iff_val, chartFraction_val, HomogeneousLocalization.val_one,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [pow_one]⟩

/-- The Segre tuple on the product chart `(i, j)`: `z_{ab}/z_{ij} = (x_a/x_i) ⊗ (y_b/y_j)`. -/
def segreTuple (i : Fin (m + 1)) (j : Fin (n + 1)) (z : Fin (segreDim m n + 1)) :
    productChartRing k m n i j :=
  chartFraction k m i (segreEquiv m n z).1 ⊗ₜ[k] chartFraction k n j (segreEquiv m n z).2

theorem segreTuple_index (i : Fin (m + 1)) (j : Fin (n + 1)) (a : Fin (m + 1)) (b : Fin (n + 1)) :
    segreTuple k m n i j ((segreEquiv m n).symm (a, b)) =
      chartFraction k m i a ⊗ₜ[k] chartFraction k n j b := by
  rw [segreTuple, (segreEquiv m n).apply_symm_apply]

theorem segreTuple_self (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreTuple k m n i j (segreIndex m n i j) = 1 := by
  rw [segreIndex, segreTuple_index, chartFraction_self, chartFraction_self]
  rfl

/-- The Segre chart ring map `A_{(z_{ij})} →+* A_{(x_i)} ⊗[k] B_{(y_j)}`. -/
abbrev segreChartHom (i : Fin (m + 1)) (j : Fin (n + 1)) :
    coordinateChartRing k (segreDim m n) (segreIndex m n i j) →+* productChartRing k m n i j :=
  tupleChartHom (segreDim m n) (algebraMap k (productChartRing k m n i j)) (segreTuple k m n i j)
    (segreIndex m n i j) (segreTuple_self k m n i j)

/-- The Segre chart map `Spec (A ⊗ B) ⟶ P^{segreDim}`. -/
abbrev segreChart (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (productChartRing k m n i j)) ⟶ projectiveSpace k (segreDim m n) :=
  tupleMorphism (segreDim m n) (algebraMap k (productChartRing k m n i j)) (segreTuple k m n i j)
    (segreIndex m n i j) (segreTuple_self k m n i j)

/-- The Segre chart map into the chart `D(z_{ij})`. -/
abbrev segreChartSpec (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (productChartRing k m n i j)) ⟶
      Spec (CommRingCat.of (coordinateChartRing k (segreDim m n) (segreIndex m n i j))) :=
  tupleSpec (segreDim m n) (algebraMap k (productChartRing k m n i j)) (segreTuple k m n i j)
    (segreIndex m n i j) (segreTuple_self k m n i j)

/-- Every Segre chart map is over `k`. -/
theorem segreChart_structure (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreChart k m n i j ≫ projectiveSpaceToSpec k (segreDim m n) =
      Spec.map (CommRingCat.ofHom (algebraMap k (productChartRing k m n i j))) :=
  tupleMorphism_structure _ _ _ _ _

/-! ## Surjectivity of the Segre chart ring map -/

theorem chartFraction_segreIndex_left (i : Fin (m + 1)) (j : Fin (n + 1)) (a : Fin (m + 1)) :
    chartFraction k (segreDim m n) (segreIndex m n i j) ((segreEquiv m n).symm (a, j)) ∈
      Set.range (chartFraction k (segreDim m n) (segreIndex m n i j)) :=
  ⟨_, rfl⟩

/-- The lift `A_{(x_i)} →+* A_{(z_{ij})}`, `x_a/x_i ↦ z_{aj}/z_{ij}`. -/
def leftLift (i : Fin (m + 1)) (j : Fin (n + 1)) :
    coordinateChartRing k m i →+* coordinateChartRing k (segreDim m n) (segreIndex m n i j) :=
  tupleChartHom m (coordinateChartConstants k (segreDim m n) (segreIndex m n i j))
    (fun a => chartFraction k (segreDim m n) (segreIndex m n i j) ((segreEquiv m n).symm (a, j)))
    i (chartFraction_self k _ _)

/-- The lift `B_{(y_j)} →+* A_{(z_{ij})}`, `y_b/y_j ↦ z_{ib}/z_{ij}`. -/
def rightLift (i : Fin (m + 1)) (j : Fin (n + 1)) :
    coordinateChartRing k n j →+* coordinateChartRing k (segreDim m n) (segreIndex m n i j) :=
  tupleChartHom n (coordinateChartConstants k (segreDim m n) (segreIndex m n i j))
    (fun b => chartFraction k (segreDim m n) (segreIndex m n i j) ((segreEquiv m n).symm (i, b)))
    j (chartFraction_self k _ _)

theorem segreChartHom_comp_leftLift (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartHom k m n i j).comp (leftLift k m n i j) = leftInclusion k m n i j := by
  apply HomogeneousAway.ringHom_ext (grading k m) (coordinate_mem k m i)
  intro d p hp
  rw [RingHom.comp_apply, leftLift, tupleChartHom_mk, tuplePolynomialHom,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, mk_eq_eval_chartFraction,
    MvPolynomial.eval₂_comp_left]
  congr 1
  · ext r
    simp only [RingHom.comp_apply, tupleChartHom_constants]
    rfl
  · funext a
    simp only [Function.comp_apply, tupleChartHom_chartFraction, segreTuple_index,
      chartFraction_self]
    rfl

theorem segreChartHom_comp_rightLift (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartHom k m n i j).comp (rightLift k m n i j) = rightInclusion k m n i j := by
  apply HomogeneousAway.ringHom_ext (grading k n) (coordinate_mem k n j)
  intro d p hp
  rw [RingHom.comp_apply, rightLift, tupleChartHom_mk, tuplePolynomialHom,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, mk_eq_eval_chartFraction,
    MvPolynomial.eval₂_comp_left]
  congr 1
  · ext r
    simp only [RingHom.comp_apply, tupleChartHom_constants]
    exact Algebra.TensorProduct.algebraMap_apply' r
  · funext b
    simp only [Function.comp_apply, tupleChartHom_chartFraction, segreTuple_index,
      chartFraction_self]
    rfl

/-- **The Segre chart ring map is surjective.** -/
theorem segreChartHom_surjective (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Function.Surjective (segreChartHom k m n i j) := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
      refine ⟨leftLift k m n i j a * rightLift k m n i j b, ?_⟩
      have hl := RingHom.congr_fun (segreChartHom_comp_leftLift k m n i j) a
      have hr := RingHom.congr_fun (segreChartHom_comp_rightLift k m n i j) b
      rw [RingHom.comp_apply] at hl hr
      rw [map_mul, hl, hr]
      change (a ⊗ₜ[k] (1 : coordinateChartRing k n j)) *
        ((1 : coordinateChartRing k m i) ⊗ₜ[k] b) = a ⊗ₜ[k] b
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨s', rfl⟩ := hy
      exact ⟨s + s', map_add _ _ _⟩

/-- **The Segre chart map is a closed immersion into the chart `D(z_{ij})`.** -/
instance segreChartSpec_isClosedImmersion (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsClosedImmersion (segreChartSpec k m n i j) :=
  tupleSpec_isClosedImmersion _ _ _ _ _ (segreChartHom_surjective k m n i j)

end KltDP.Geometry.ProjectiveSegreGeneral
