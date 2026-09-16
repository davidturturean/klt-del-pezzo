import KltDP.Geometry.ProjectiveSegreCharts
import KltDP.Geometry.ProjectiveLineChartFunctions
import KltDP.Geometry.ClosedImmersionOfChartSquares
import KltDP.Examples.FrobeniusGraphPicardClassCharts
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The Segre morphism `P¹ ×_k P¹ ⟶ P³`

The four Segre chart maps `segreChart k i j : Spec k[u][v] ⟶ P³` are glued over the accepted
four-chart cover of `projectiveProduct k` (`productChart i j`, lifted to the universe of the pinned
gluing API as `liftedProductCover`) with the pinned `Scheme.Cover.glueMorphisms`:

* on the overlap `W = pullback (productChart i j) (productChart i' j')` the two chart maps are
  compared through the ring maps `Γ(W, ⊤) ← k[u][v]` of the two projections
  (`specHomRingHom`, no affine description of `W` is needed): the first coordinate functions are
  equal for `i = i'` and mutually inverse for `i ≠ i'` (the accepted `P¹` overlap, through
  `chart_function_relation`), likewise the second ones, and constants agree; this is the scaling
  identity of `segreChart_compatible` (`segre_glue_compatible`);
* `segreMorphism : projectiveProduct k ⟶ projectiveSpace k 3` with
  `productChart_segreMorphism : productChart i j ≫ segreMorphism = segreChart i j`, and
  `segreMorphism_structure`: it is over `k` (`segreMorphism ≫ projectiveSpaceToSpec k 3 =
  projectiveProductToSpec`).

The closed-immersion conclusion and `IsProjectiveOverField projectiveProductToSpec` are stated with
the range identity `range (productChart i j) = σ⁻¹(D(z_{ij}))` as an explicit hypothesis
(`segreMorphism_isClosedImmersion`, `projectiveProduct_isProjectiveOverField_of_range`); that
identity is not proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveSegreCover

open ProjectiveChart ProjectiveLineComparison
open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth
open KltDP.Examples.FrobeniusProjectivePoints KltDP.Examples.FrobeniusProductPlaneChart
open KltDP.Examples.FrobeniusGraphPicardClassCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

theorem segreIndex_row_col (z : Fin (3 + 1)) : segreIndex (segreRow z, segreCol z) = z :=
  Fin.ext (by change 2 * (z.val / 2) + z.val % 2 = z.val; omega)

theorem fin_two_eq_or : ∀ a i : Fin 2, a = i ∨ a = i + 1 := by decide

/-- Every product chart is over `k`. -/
theorem productChart_toSpec (i j : Fin 2) :
    productChart (k := k) i j ≫ projectiveProductToSpec =
      Spec.map (CommRingCat.ofHom planeConstants) := by
  rw [projectiveProductToSpec, ← Category.assoc, productChart_fst, Category.assoc,
    polynomialChartMap_structureMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

section Factor

variable {k} {S : Type u} [CommRing S]

/-- The one-factor scaling identity, from the relation between the coordinate functions. -/
theorem factor_scale (α β : planeRing k →+* S) (c : planeRing k) (i i' a : Fin 2)
    (heq : i = i' → α c = β c) (hmul : i ≠ i' → α c * β c = 1) :
    α (if a = i then 1 else c) = α (if i' = i then 1 else c) * β (if a = i' then 1 else c) := by
  rcases fin_two_eq_or a i with ha | ha <;> rcases fin_two_eq_or i' i with hi | hi
  · rw [if_pos ha, if_pos hi, if_pos (ha.trans hi.symm), map_one, map_one, mul_one]
  · have hne : i ≠ i' := by rw [hi]; exact (fin_two_add_one_ne i).symm
    rw [if_pos ha, if_neg (Ne.symm hne), if_neg (by rw [ha]; exact hne), map_one]
    exact (hmul hne).symm
  · rw [if_neg (by rw [ha]; exact fin_two_add_one_ne i), if_pos hi,
      if_neg (by rw [ha, hi]; exact fin_two_add_one_ne i), map_one, one_mul]
    exact heq hi.symm
  · rw [if_neg (by rw [ha]; exact fin_two_add_one_ne i),
      if_neg (by rw [hi]; exact fin_two_add_one_ne i), if_pos (ha.trans hi.symm), map_one,
      mul_one]

end Factor

section Overlap

variable {k} (i j i' j' : Fin 2)

/-- The coordinate ring map of the first projection of the overlap of two product charts. -/
abbrev overlapLeft :=
  (specHomRingHom (pullback.fst (productChart (k := k) i j) (productChart (k := k) i' j'))).hom

/-- The coordinate ring map of the second projection of the overlap of two product charts. -/
abbrev overlapRight :=
  (specHomRingHom (pullback.snd (productChart (k := k) i j) (productChart (k := k) i' j'))).hom

theorem overlap_first :
    (pullback.fst (productChart (k := k) i j) (productChart (k := k) i' j') ≫
        Spec.map (CommRingCat.ofHom firstCoordinateMap)) ≫ polynomialChartMap k i =
      (pullback.snd (productChart (k := k) i j) (productChart (k := k) i' j') ≫
        Spec.map (CommRingCat.ofHom firstCoordinateMap)) ≫ polynomialChartMap k i' := by
  rw [Category.assoc, Category.assoc, ← productChart_fst, ← productChart_fst, ← Category.assoc,
    ← Category.assoc, pullback.condition]

theorem overlap_second :
    (pullback.fst (productChart (k := k) i j) (productChart (k := k) i' j') ≫
        Spec.map (CommRingCat.ofHom secondCoordinateMap)) ≫ polynomialChartMap k j =
      (pullback.snd (productChart (k := k) i j) (productChart (k := k) i' j') ≫
        Spec.map (CommRingCat.ofHom secondCoordinateMap)) ≫ polynomialChartMap k j' := by
  rw [Category.assoc, Category.assoc, ← productChart_snd, ← productChart_snd, ← Category.assoc,
    ← Category.assoc, pullback.condition]

/-- The first coordinates of the two projections: equal on a common chart, inverse otherwise. -/
theorem overlap_u_relation :
    (i = i' → overlapLeft (k := k) i j i' j' uCoord = overlapRight (k := k) i j i' j' uCoord) ∧
      (i ≠ i' → overlapLeft (k := k) i j i' j' uCoord * overlapRight (k := k) i j i' j' uCoord = 1) := by
  have h := chart_function_relation k _ _ i i' (overlap_first i j i' j')
  rw [specHomRingHom_comp_specMap, specHomRingHom_comp_specMap] at h
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    firstCoordinateMap_X] using h

/-- The second coordinates of the two projections: equal on a common chart, inverse otherwise. -/
theorem overlap_v_relation :
    (j = j' → overlapLeft (k := k) i j i' j' vCoord = overlapRight (k := k) i j i' j' vCoord) ∧
      (j ≠ j' → overlapLeft (k := k) i j i' j' vCoord * overlapRight (k := k) i j i' j' vCoord = 1) := by
  have h := chart_function_relation k _ _ j j' (overlap_second i j i' j')
  rw [specHomRingHom_comp_specMap, specHomRingHom_comp_specMap] at h
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    secondCoordinateMap_X] using h

/-- Constants agree on the overlap. -/
theorem overlap_constants (r : k) :
    overlapLeft (k := k) i j i' j' (planeConstants r) = overlapRight (k := k) i j i' j' (planeConstants r) := by
  have hc : pullback.fst (productChart (k := k) i j) (productChart (k := k) i' j') ≫
        Spec.map (CommRingCat.ofHom planeConstants) =
      pullback.snd (productChart (k := k) i j) (productChart (k := k) i' j') ≫
        Spec.map (CommRingCat.ofHom planeConstants) := by
    calc pullback.fst (productChart (k := k) i j) (productChart (k := k) i' j') ≫
          Spec.map (CommRingCat.ofHom planeConstants)
        = pullback.fst (productChart (k := k) i j) (productChart (k := k) i' j') ≫
            (productChart (k := k) i j ≫ projectiveProductToSpec) := by
          rw [productChart_toSpec]
      _ = pullback.snd (productChart (k := k) i j) (productChart (k := k) i' j') ≫
            (productChart (k := k) i' j' ≫ projectiveProductToSpec) := by
          rw [← Category.assoc, ← Category.assoc, pullback.condition]
      _ = _ := by rw [productChart_toSpec]
  have h := specHomRingHom_congr hc
  have := congrArg (fun φ : CommRingCat.of k ⟶
    Γ(pullback (productChart (k := k) i j) (productChart (k := k) i' j'), ⊤) => φ.hom r) h
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using this

/-- The scaling identity on the overlap of two product charts. -/
theorem overlap_scale (z : Fin (3 + 1)) :
    overlapLeft (k := k) i j i' j' (segreImage k i j z) =
      scaleFactor i j i' j' (overlapLeft (k := k) i j i' j') *
        overlapRight (k := k) i j i' j' (segreImage k i' j' z) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, z = segreIndex (a, b) :=
    ⟨segreRow z, segreCol z, (segreIndex_row_col z).symm⟩
  dsimp only [scaleFactor]
  rw [segreImage_index, segreImage_index, segreImage_index, map_mul, map_mul, map_mul,
    factor_scale _ _ uCoord i i' a (overlap_u_relation i j i' j').1
      (overlap_u_relation i j i' j').2,
    factor_scale _ _ vCoord j j' b (overlap_v_relation i j i' j').1
      (overlap_v_relation i j i' j').2]
  ring

/-- **The Segre chart maps agree on the overlaps of the product charts.** -/
theorem segre_glue_compatible :
    pullback.fst (productChart (k := k) i j) (productChart (k := k) i' j') ≫ segreChart k i j =
      pullback.snd (productChart (k := k) i j) (productChart (k := k) i' j') ≫
        segreChart k i' j' := by
  rw [specHom_eq_toSpecΓ (pullback.fst (productChart (k := k) i j) (productChart (k := k) i' j')),
    specHom_eq_toSpecΓ (pullback.snd (productChart (k := k) i j) (productChart (k := k) i' j')),
    Category.assoc, Category.assoc]
  congr 1
  have := segreChart_compatible i j i' j' (overlapLeft (k := k) i j i' j') (overlapRight (k := k) i j i' j')
    (overlap_constants i j i' j') (overlap_scale i j i' j')
  simpa only [CommRingCat.ofHom_hom] using this

end Overlap

/-- The accepted four product charts as an open cover with universe-lifted index. -/
def liftedProductCover : Scheme.OpenCover.{u} (projectiveProduct k) where
  J := ULift.{u} (Fin 2) × ULift.{u} (Fin 2)
  obj _ := Spec (CommRingCat.of (planeRing k))
  map ij := productChart ij.1.down ij.2.down
  f x := (⟨((productCover (k := k)).f x).1⟩, ⟨((productCover (k := k)).f x).2⟩)
  covers x := (productCover (k := k)).covers x

@[simp] theorem liftedProductCover_map (ij : ULift.{u} (Fin 2) × ULift.{u} (Fin 2)) :
    (liftedProductCover k).map ij = productChart ij.1.down ij.2.down := rfl

/-- **The Segre morphism** `P¹ ×_k P¹ ⟶ P³`, glued from the four chart maps. -/
def segreMorphism : projectiveProduct k ⟶ projectiveSpace k 3 :=
  (liftedProductCover k).glueMorphisms (fun ij => segreChart k ij.1.down ij.2.down)
    (fun ij ij' => segre_glue_compatible ij.1.down ij.2.down ij'.1.down ij'.2.down)

/-- On each product chart the Segre morphism is the Segre chart map. -/
theorem productChart_segreMorphism (i j : Fin 2) :
    productChart (k := k) i j ≫ segreMorphism k = segreChart k i j :=
  (liftedProductCover k).ι_glueMorphisms _ _ (⟨i⟩, ⟨j⟩)

/-- The Segre morphism is over `k`. -/
theorem segreMorphism_structure :
    segreMorphism k ≫ projectiveSpaceToSpec k 3 = projectiveProductToSpec := by
  apply (liftedProductCover k).hom_ext
  intro ij
  rw [liftedProductCover_map, ← Category.assoc, productChart_segreMorphism, segreChart_structure,
    productChart_toSpec]
  rfl

/-- The coordinate charts of `P³` indexed by the product-chart indices. -/
def segreTargetCover : Scheme.OpenCover.{u} (projectiveSpace k 3) where
  J := ULift.{u} (Fin 2) × ULift.{u} (Fin 2)
  obj ij := Spec (CommRingCat.of (coordinateChartRing k 3 (segreIndex (ij.1.down, ij.2.down))))
  map ij := coordinateChartMorphism k 3 (segreIndex (ij.1.down, ij.2.down))
  f x := (⟨segreRow ((standardAffineCover k 3).f x)⟩, ⟨segreCol ((standardAffineCover k 3).f x)⟩)
  covers x := by
    have h := (standardAffineCover k 3).covers x
    rw [← segreIndex_row_col ((standardAffineCover k 3).f x)] at h
    exact h

/-- The Segre morphism is a closed immersion, given the range identity
`range (productChart i j) = σ⁻¹(D(z_{ij}))` on the four charts. -/
theorem segreMorphism_isClosedImmersion
    (hrange : ∀ i j : Fin 2, Set.range (productChart (k := k) i j).base =
      (segreMorphism k).base ⁻¹'
        Set.range (coordinateChartMorphism k 3 (segreIndex (i, j))).base) :
    IsClosedImmersion (segreMorphism k) :=
  isClosedImmersion_of_chartSquares (segreMorphism k) (segreTargetCover k)
    (fun _ => Spec (CommRingCat.of (planeRing k)))
    (fun ij => productChart ij.1.down ij.2.down)
    (fun ij => segreChartSpec k ij.1.down ij.2.down)
    (fun ij => productChart_segreMorphism k ij.1.down ij.2.down)
    (fun ij => hrange ij.1.down ij.2.down)

/-- `P¹ ×_k P¹` is projective over `k`, given the range identity on the four charts. -/
theorem projectiveProduct_isProjectiveOverField_of_range
    (hrange : ∀ i j : Fin 2, Set.range (productChart (k := k) i j).base =
      (segreMorphism k).base ⁻¹'
        Set.range (coordinateChartMorphism k 3 (segreIndex (i, j))).base) :
    IsProjectiveOverField (projectiveProductToSpec (k := k)) :=
  ⟨3, segreMorphism k, segreMorphism_isClosedImmersion k hrange, segreMorphism_structure k⟩

end KltDP.Geometry.ProjectiveSegreCover
