import KltDP.Geometry.ProjectiveSegreGeneralCharts
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The Segre morphism `P^m ×_k P^n ⟶ P^{(m+1)(n+1)-1}` (DRAFT — untested, see the F09 record)

On the overlap of two product charts `(i, j)`, `(i', j')` the pulled-back coordinate fractions satisfy
the chart-transition relations of `P^m` and `P^n` separately (`left_relation_mul`,
`right_relation_mul`, from `chart_relation_mul` of `ProjectiveSpaceChartFunctionsGeneral` applied to
the two projections), constants agree (`overlap_constants`), and therefore the Segre tuples satisfy the
scaling identity of `tupleMorphism_eq_of_scale` (`segre_scale`). The Segre chart maps glue over
`segreCover` (the product charts as an `OpenCover.{u}`) to **`segreMorphism : P^m ×_k P^n ⟶ P^{segreDim}`**,
with `productChart_segreMorphism` and `segreMorphism_structure` (over `k`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.ProjectiveSegreGeneral

open KltDP.Geometry.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (m n : ℕ)

theorem tmul_eq_mul {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (x : A) (y : B) : x ⊗ₜ[k] y = (x ⊗ₜ[k] (1 : B)) * ((1 : A) ⊗ₜ[k] y) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

section Overlap

variable {k m n} {W : Scheme.{u}} (i i' : Fin (m + 1)) (j j' : Fin (n + 1))
  (g₀ : W ⟶ Spec (CommRingCat.of (productChartRing k m n i j)))
  (g₁ : W ⟶ Spec (CommRingCat.of (productChartRing k m n i' j')))
  (h : g₀ ≫ productChart k m n i j = g₁ ≫ productChart k m n i' j')

include h in
theorem overlap_left_condition :
    (g₀ ≫ Spec.map (CommRingCat.ofHom (leftInclusion k m n i j))) ≫ coordinateChartMorphism k m i =
      (g₁ ≫ Spec.map (CommRingCat.ofHom (leftInclusion k m n i' j'))) ≫
        coordinateChartMorphism k m i' := by
  rw [Category.assoc, Category.assoc, ← productChart_fst, ← productChart_fst, ← Category.assoc,
    ← Category.assoc, h]

include h in
theorem overlap_right_condition :
    (g₀ ≫ Spec.map (CommRingCat.ofHom (rightInclusion k m n i j))) ≫ coordinateChartMorphism k n j =
      (g₁ ≫ Spec.map (CommRingCat.ofHom (rightInclusion k m n i' j'))) ≫
        coordinateChartMorphism k n j' := by
  rw [Category.assoc, Category.assoc, ← productChart_snd, ← productChart_snd, ← Category.assoc,
    ← Category.assoc, h]

theorem specHomRingHom_comp_left :
    (specHomRingHom (g₀ ≫ Spec.map (CommRingCat.ofHom (leftInclusion k m n i j)))).hom =
      (specHomRingHom g₀).hom.comp (leftInclusion k m n i j) := by
  rw [specHomRingHom_comp_specMap]
  rfl

theorem specHomRingHom_comp_right :
    (specHomRingHom (g₀ ≫ Spec.map (CommRingCat.ofHom (rightInclusion k m n i j)))).hom =
      (specHomRingHom g₀).hom.comp (rightInclusion k m n i j) := by
  rw [specHomRingHom_comp_specMap]
  rfl

include h in
/-- The first-factor relation on the overlap. -/
theorem left_relation_mul (a : Fin (m + 1)) :
    (specHomRingHom g₀).hom (chartFraction k m i a ⊗ₜ[k] (1 : coordinateChartRing k n j)) =
      (specHomRingHom g₀).hom (chartFraction k m i i' ⊗ₜ[k] (1 : coordinateChartRing k n j)) *
        (specHomRingHom g₁).hom
          (chartFraction k m i' a ⊗ₜ[k] (1 : coordinateChartRing k n j')) := by
  have := chart_relation_mul i i' _ _ (overlap_left_condition i i' j j' g₀ g₁ h) a
  rw [specHomRingHom_comp_left, specHomRingHom_comp_left] at this
  exact this

include h in
/-- The second-factor relation on the overlap. -/
theorem right_relation_mul (b : Fin (n + 1)) :
    (specHomRingHom g₀).hom ((1 : coordinateChartRing k m i) ⊗ₜ[k] chartFraction k n j b) =
      (specHomRingHom g₀).hom ((1 : coordinateChartRing k m i) ⊗ₜ[k] chartFraction k n j j') *
        (specHomRingHom g₁).hom
          ((1 : coordinateChartRing k m i') ⊗ₜ[k] chartFraction k n j' b) := by
  have := chart_relation_mul j j' _ _ (overlap_right_condition i i' j j' g₀ g₁ h) b
  rw [specHomRingHom_comp_right, specHomRingHom_comp_right] at this
  exact this

include h in
/-- Constants agree on the overlap. -/
theorem overlap_constants :
    (specHomRingHom g₀).hom.comp (algebraMap k (productChartRing k m n i j)) =
      (specHomRingHom g₁).hom.comp (algebraMap k (productChartRing k m n i' j')) := by
  have hc : g₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (productChartRing k m n i j))) =
      g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (productChartRing k m n i' j'))) := by
    calc g₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (productChartRing k m n i j)))
        = g₀ ≫ (productChart k m n i j ≫ projectiveProductSpaceToSpec k m n) := by
          rw [productChart_toSpec]
      _ = g₁ ≫ (productChart k m n i' j' ≫ projectiveProductSpaceToSpec k m n) := by
          rw [← Category.assoc, h, Category.assoc]
      _ = _ := by rw [productChart_toSpec]
  have h2 := congrArg CommRingCat.Hom.hom (specHomRingHom_congr hc)
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using h2

include h in
/-- **The scaling identity of the Segre tuples on the overlap.** -/
theorem segre_scale (z : Fin (segreDim m n + 1)) :
    (specHomRingHom g₀).hom (segreTuple k m n i j z) =
      (specHomRingHom g₀).hom (segreTuple k m n i j (segreIndex m n i' j')) *
        (specHomRingHom g₁).hom (segreTuple k m n i' j' z) := by
  rw [segreIndex, segreTuple_index, segreTuple, segreTuple]
  set a := (segreEquiv m n z).1 with ha
  set b := (segreEquiv m n z).2 with hb
  rw [tmul_eq_mul k (chartFraction k m i a) (chartFraction k n j b),
    tmul_eq_mul k (chartFraction k m i i') (chartFraction k n j j'),
    tmul_eq_mul k (chartFraction k m i' a) (chartFraction k n j' b), map_mul, map_mul, map_mul,
    left_relation_mul i i' j j' g₀ g₁ h a, right_relation_mul i i' j j' g₀ g₁ h b]
  ring

include h in
/-- **Two Segre chart maps agree on the overlap of their product charts.** -/
theorem segreChart_compatible :
    g₀ ≫ segreChart k m n i j = g₁ ≫ segreChart k m n i' j' := by
  have h1 := comp_tupleMorphism (segreDim m n) (algebraMap k (productChartRing k m n i j))
    (segreTuple k m n i j) (segreIndex m n i j) (segreTuple_self k m n i j) g₀
  have h2 := comp_tupleMorphism (segreDim m n) (algebraMap k (productChartRing k m n i' j'))
    (segreTuple k m n i' j') (segreIndex m n i' j') (segreTuple_self k m n i' j') g₁
  have h3 := tupleMorphism_eq_of_scale
    ((specHomRingHom g₀).hom.comp (algebraMap k (productChartRing k m n i j)))
    ((specHomRingHom g₀).hom ∘ segreTuple k m n i j)
    ((specHomRingHom g₁).hom ∘ segreTuple k m n i' j')
    (segreIndex m n i j) (segreIndex m n i' j')
    (by simp only [Function.comp_apply, segreTuple_self, map_one])
    (by simp only [Function.comp_apply, segreTuple_self, map_one])
    (segre_scale i i' j j' g₀ g₁ h)
  have h4 : tupleMorphism (segreDim m n)
      ((specHomRingHom g₀).hom.comp (algebraMap k (productChartRing k m n i j)))
      ((specHomRingHom g₁).hom ∘ segreTuple k m n i' j') (segreIndex m n i' j')
      (by simp only [Function.comp_apply, segreTuple_self, map_one]) =
    tupleMorphism (segreDim m n)
      ((specHomRingHom g₁).hom.comp (algebraMap k (productChartRing k m n i' j')))
      ((specHomRingHom g₁).hom ∘ segreTuple k m n i' j') (segreIndex m n i' j')
      (by simp only [Function.comp_apply, segreTuple_self, map_one]) := by
    rw [overlap_constants i i' j j' g₀ g₁ h]
  change g₀ ≫ tupleMorphism _ _ _ _ _ = g₁ ≫ tupleMorphism _ _ _ _ _
  rw [h1, h2, h3, h4]

end Overlap

/-! ## Gluing -/

/-- The product charts as an open cover with `Spec (A ⊗[k] B)` pieces. -/
def segreCover : Scheme.OpenCover.{u} (projectiveProductSpace k m n) where
  J := ULift.{u} (Fin (m + 1)) × ULift.{u} (Fin (n + 1))
  obj ij := Spec (CommRingCat.of (productChartRing k m n ij.1.down ij.2.down))
  map ij := productChart k m n ij.1.down ij.2.down
  f x := (⟨(exists_productChart k m n x).choose⟩, ⟨(exists_productChart k m n x).choose_spec.choose⟩)
  covers x := (exists_productChart k m n x).choose_spec.choose_spec

@[simp] theorem segreCover_map (ij : ULift.{u} (Fin (m + 1)) × ULift.{u} (Fin (n + 1))) :
    (segreCover k m n).map ij = productChart k m n ij.1.down ij.2.down := rfl

/-- **The Segre morphism** `P^m ×_k P^n ⟶ P^{(m+1)(n+1)-1}`. -/
def segreMorphism : projectiveProductSpace k m n ⟶ projectiveSpace k (segreDim m n) :=
  (segreCover k m n).glueMorphisms (fun ij => segreChart k m n ij.1.down ij.2.down)
    (fun ij ij' => segreChart_compatible ij.1.down ij'.1.down ij.2.down ij'.2.down _ _
      pullback.condition)

/-- On each product chart the Segre morphism is the Segre chart map. -/
theorem productChart_segreMorphism (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productChart k m n i j ≫ segreMorphism k m n = segreChart k m n i j :=
  (segreCover k m n).ι_glueMorphisms _ _ (⟨i⟩, ⟨j⟩)

/-- The Segre morphism is over `k`. -/
theorem segreMorphism_structure :
    segreMorphism k m n ≫ projectiveSpaceToSpec k (segreDim m n) =
      projectiveProductSpaceToSpec k m n := by
  apply (segreCover k m n).hom_ext
  intro ij
  rw [segreCover_map, ← Category.assoc, productChart_segreMorphism, segreChart_structure,
    productChart_toSpec]

end KltDP.Geometry.ProjectiveSegreGeneral
