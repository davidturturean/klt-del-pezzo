import KltDP.Geometry.ProjectiveSpaceCoordinateCharts
import KltDP.Examples.FrobeniusBlowupSmooth

/-!
# The four Segre chart maps `Spec k[u][v] ⟶ P³` and their compatibility on overlaps

The Segre map `[x₀:x₁] × [y₀:y₁] ↦ [z_{ab} = x_a y_b]` on the product chart `(i, j)`
(coordinates `u = x_{i+1}/x_i`, `v = y_{j+1}/y_j`) lands in the chart `D(z_{ij})` of `P³` and sends
`z_{ab}/z_{ij} ↦ u^{[a ≠ i]} v^{[b ≠ j]}` (`segreImage`). Each chart map is the spectrum of the lift
`segreChartHom i j : (k[z]_{(z_{ij})}) →+* k[u][v]` of the polynomial substitution
`segrePolynomialHom i j`, followed by the accepted coordinate chart of `z_{ij}`:

* `segreChartHom_surjective` (explicit right inverse `planeToChart`), hence `segreChartSpec i j` is a
  closed immersion and `segreChart i j = segreChartSpec i j ≫ coordinateChartMorphism k 3 z_{ij}`;
* `segreChart_structure`: every chart map is over `k`;
* `segreChart_compatible`: for any ring `S` and `α β : k[u][v] →+* S` agreeing on constants and
  satisfying the scaling identity `α(image_{ij} z) = α(image_{ij} z_{i'j'}) · β(image_{i'j'} z)` for
  all four coordinates `z`, one has `Spec.map α ≫ segreChart i j = Spec.map β ≫ segreChart i' j'`.
  (Both sides factor through the overlap chart `D(z_{ij} z_{i'j'})` via the lift of `α ∘ φ_{ij}`; the
  identity on homogeneous fractions is the accepted `homogeneous_eval₂_scale`.)

The affine descriptions of the product-chart overlaps supplying `S`, `α`, `β` are not part of this
module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveSegreCover

open ProjectiveChart KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The coordinate `z_{ab} = x_a y_b` of `P³`, indexed by `2a + b`. -/
def segreIndex (ab : Fin 2 × Fin 2) : Fin (3 + 1) := ⟨2 * ab.1.val + ab.2.val, by omega⟩

/-- The row `a` of a coordinate `z_{ab}`. -/
def segreRow (z : Fin (3 + 1)) : Fin 2 := ⟨z.val / 2, by omega⟩

/-- The column `b` of a coordinate `z_{ab}`. -/
def segreCol (z : Fin (3 + 1)) : Fin 2 := ⟨z.val % 2, by omega⟩

theorem segreRow_index (a b : Fin 2) : segreRow (segreIndex (a, b)) = a :=
  Fin.ext (by change (2 * a.val + b.val) / 2 = a.val; omega)

theorem segreCol_index (a b : Fin 2) : segreCol (segreIndex (a, b)) = b :=
  Fin.ext (by change (2 * a.val + b.val) % 2 = b.val; omega)

/-- The image of `z_{ab}/z_{ij}` on the product chart `(i, j)`: `u^{[a ≠ i]} v^{[b ≠ j]}`. -/
def segreImage (i j : Fin 2) (z : Fin (3 + 1)) : planeRing k :=
  (if segreRow z = i then 1 else uCoord) * (if segreCol z = j then 1 else vCoord)

theorem segreImage_index (i j a b : Fin 2) :
    segreImage k i j (segreIndex (a, b)) =
      (if a = i then 1 else uCoord) * (if b = j then 1 else vCoord) := by
  rw [segreImage, segreRow_index, segreCol_index]

theorem segreImage_center (i j : Fin 2) : segreImage k i j (segreIndex (i, j)) = 1 := by
  rw [segreImage_index, if_pos rfl, if_pos rfl, mul_one]

/-- The polynomial substitution `z_{ab} ↦ u^{[a ≠ i]} v^{[b ≠ j]}`, coefficients fixed. -/
def segrePolynomialHom (i j : Fin 2) : homogeneousRing k 3 →+* planeRing k :=
  MvPolynomial.eval₂Hom planeConstants (segreImage k i j)

@[simp] theorem segrePolynomialHom_C (i j : Fin 2) (r : k) :
    segrePolynomialHom k i j (MvPolynomial.C r) = planeConstants r :=
  MvPolynomial.eval₂Hom_C _ _ r

@[simp] theorem segrePolynomialHom_X (i j : Fin 2) (z : Fin (3 + 1)) :
    segrePolynomialHom k i j (MvPolynomial.X z) = segreImage k i j z :=
  MvPolynomial.eval₂Hom_X' _ _ z

theorem segrePolynomialHom_center (i j : Fin 2) :
    segrePolynomialHom k i j (MvPolynomial.X (segreIndex (i, j))) = 1 := by
  rw [segrePolynomialHom_X, segreImage_center]

/-- The Segre chart ring map `k[z]_{(z_{ij})} →+* k[u][v]`. -/
def segreChartHom (i j : Fin 2) :
    coordinateChartRing k 3 (segreIndex (i, j)) →+* planeRing k :=
  HomogeneousAway.lift (grading k 3) (segrePolynomialHom k i j) 1
    (by rw [segrePolynomialHom_center, mul_one])

theorem segreChartHom_mk (i j : Fin 2) (m : ℕ) (a : homogeneousRing k 3)
    (ha : a ∈ grading k 3 (m • 1)) :
    segreChartHom k i j
        (HomogeneousLocalization.Away.mk (grading k 3) (coordinate_mem k 3 (segreIndex (i, j)))
          m a ha) =
      segrePolynomialHom k i j a := by
  rw [segreChartHom, HomogeneousAway.lift_mk, one_pow, mul_one]

@[simp] theorem segreChartHom_constants (i j : Fin 2) (r : k) :
    segreChartHom k i j (coordinateChartConstants k 3 (segreIndex (i, j)) r) = planeConstants r := by
  rw [segreChartHom, coordinateChartConstants, RingHom.comp_apply,
    HomogeneousAway.lift_fromZeroRingHom]
  exact segrePolynomialHom_C k i j r

/-- The fraction `u = z_{(i+1) j} / z_{ij}`. -/
def ratioU (i j : Fin 2) : coordinateChartRing k 3 (segreIndex (i, j)) :=
  HomogeneousLocalization.Away.mk (grading k 3) (coordinate_mem k 3 (segreIndex (i, j))) 1
    (MvPolynomial.X (segreIndex (i + 1, j)))
    (by simpa only [one_smul] using coordinate_mem k 3 (segreIndex (i + 1, j)))

/-- The fraction `v = z_{i (j+1)} / z_{ij}`. -/
def ratioV (i j : Fin 2) : coordinateChartRing k 3 (segreIndex (i, j)) :=
  HomogeneousLocalization.Away.mk (grading k 3) (coordinate_mem k 3 (segreIndex (i, j))) 1
    (MvPolynomial.X (segreIndex (i, j + 1)))
    (by simpa only [one_smul] using coordinate_mem k 3 (segreIndex (i, j + 1)))

theorem fin_two_add_one_ne (i : Fin 2) : i + 1 ≠ i := by
  fin_cases i <;> decide

@[simp] theorem segreChartHom_ratioU (i j : Fin 2) :
    segreChartHom k i j (ratioU k i j) = uCoord := by
  rw [ratioU, segreChartHom_mk, segrePolynomialHom_X, segreImage_index,
    if_neg (fin_two_add_one_ne i), if_pos rfl, mul_one]

@[simp] theorem segreChartHom_ratioV (i j : Fin 2) :
    segreChartHom k i j (ratioV k i j) = vCoord := by
  rw [ratioV, segreChartHom_mk, segrePolynomialHom_X, segreImage_index,
    if_neg (fin_two_add_one_ne j), if_pos rfl, one_mul]

/-- The right inverse `u ↦ z_{(i+1)j}/z_{ij}`, `v ↦ z_{i(j+1)}/z_{ij}`. -/
def planeToChart (i j : Fin 2) : planeRing k →+* coordinateChartRing k 3 (segreIndex (i, j)) :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (coordinateChartConstants k 3 (segreIndex (i, j))) (ratioU k i j))
    (ratioV k i j)

theorem segreChartHom_comp_planeToChart (i j : Fin 2) :
    (segreChartHom k i j).comp (planeToChart k i j) = RingHom.id (planeRing k) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro r
      simp [planeToChart, planeConstants]
    · simp [planeToChart, uCoord]
  · simp [planeToChart, vCoord]

/-- The Segre chart ring map is surjective. -/
theorem segreChartHom_surjective (i j : Fin 2) : Function.Surjective (segreChartHom k i j) :=
  fun x => ⟨planeToChart k i j x, RingHom.congr_fun (segreChartHom_comp_planeToChart k i j) x⟩

/-- The Segre map on the product chart `(i, j)` into the chart `D(z_{ij})`. -/
def segreChartSpec (i j : Fin 2) :
    Spec (CommRingCat.of (planeRing k)) ⟶
      Spec (CommRingCat.of (coordinateChartRing k 3 (segreIndex (i, j)))) :=
  Spec.map (CommRingCat.ofHom (segreChartHom k i j))

instance segreChartSpec_isClosedImmersion (i j : Fin 2) :
    IsClosedImmersion (segreChartSpec k i j) :=
  IsClosedImmersion.spec_of_surjective _ (segreChartHom_surjective k i j)

/-- The Segre map on the product chart `(i, j)`, into `P³`. -/
def segreChart (i j : Fin 2) : Spec (CommRingCat.of (planeRing k)) ⟶ projectiveSpace k 3 :=
  segreChartSpec k i j ≫ coordinateChartMorphism k 3 (segreIndex (i, j))

/-- Every Segre chart map is over `k`. -/
theorem segreChart_structure (i j : Fin 2) :
    segreChart k i j ≫ projectiveSpaceToSpec k 3 = planeStructure := by
  rw [segreChart, Category.assoc, coordinateChartMorphism_over_base, segreChartSpec, planeStructure,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun r => segreChartHom_constants k i j r)

section Compatibility

variable {k} {S : Type u} [CommRing S] (i j i' j' : Fin 2) (α β : planeRing k →+* S)

/-- The scaling factor between the two charts: `α(image_{ij} z_{i'j'})`. -/
abbrev scaleFactor : S := α (segreImage k i j (segreIndex (i', j')))

variable (hconst : ∀ r : k, α (planeConstants r) = β (planeConstants r))
  (hscale : ∀ z : Fin (3 + 1),
    α (segreImage k i j z) = scaleFactor i j i' j' α * β (segreImage k i' j' z))

include hconst hscale in
/-- On a homogeneous polynomial of degree `d` the two substitutions differ by the `d`-th power of
the scaling factor. -/
theorem scaled_apply (a : homogeneousRing k 3) {d : ℕ} (ha : a.IsHomogeneous d) :
    α (segrePolynomialHom k i j a) =
      scaleFactor i j i' j' α ^ d * β (segrePolynomialHom k i' j' a) := by
  have h1 : α.comp (segrePolynomialHom k i j) =
      MvPolynomial.eval₂Hom (α.comp planeConstants)
        (fun z => scaleFactor i j i' j' α * β (segreImage k i' j' z)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro z
      simp only [RingHom.comp_apply, segrePolynomialHom_X, MvPolynomial.eval₂Hom_X']
      exact hscale z
  have h2 : β.comp (segrePolynomialHom k i' j') =
      MvPolynomial.eval₂Hom (α.comp planeConstants) (fun z => β (segreImage k i' j' z)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [hconst]
    · intro z
      simp
  change (α.comp (segrePolynomialHom k i j)) a =
    scaleFactor i j i' j' α ^ d * (β.comp (segrePolynomialHom k i' j')) a
  rw [h1, h2]
  exact homogeneous_eval₂_scale ha (α.comp planeConstants)
    (fun z => β (segreImage k i' j' z)) (scaleFactor i j i' j' α)

include hscale in
/-- The scaling factor is invertible, with inverse `β(image_{i'j'} z_{ij})`. -/
theorem scaleFactor_mul :
    scaleFactor i j i' j' α * β (segreImage k i' j' (segreIndex (i, j))) = 1 := by
  have h := hscale (segreIndex (i, j))
  rw [segreImage_center, map_one] at h
  exact h.symm

/-- The common map from the overlap chart ring `k[z]_{(z_{ij} z_{i'j'})}`. -/
def overlapHom : coordinateOverlapRing k 3 (segreIndex (i, j)) (segreIndex (i', j')) →+* S :=
  HomogeneousAway.lift (grading k 3) (α.comp (segrePolynomialHom k i j))
    (β (segreImage k i' j' (segreIndex (i, j))))
    (by
      rw [RingHom.comp_apply, map_mul, segrePolynomialHom_center, one_mul, segrePolynomialHom_X]
      exact scaleFactor_mul i j i' j' α β hscale)

include hscale in
theorem overlapHom_left :
    α.comp (segreChartHom k i j) =
      (overlapHom i j i' j' α β hscale).comp
        (toOverlapLeft k 3 (segreIndex (i, j)) (segreIndex (i', j'))) := by
  apply HomogeneousAway.ringHom_ext (grading k 3) (coordinate_mem k 3 (segreIndex (i, j)))
  intro n a ha
  rw [RingHom.comp_apply, RingHom.comp_apply, segreChartHom_mk, toOverlapLeft,
    HomogeneousLocalization.awayMap_mk, overlapHom, HomogeneousAway.lift_mk,
    RingHom.comp_apply, map_mul, map_pow, segrePolynomialHom_X, map_mul, map_pow, mul_assoc,
    ← mul_pow, scaleFactor_mul i j i' j' α β hscale, one_pow, mul_one]

include hconst hscale in
theorem overlapHom_right :
    β.comp (segreChartHom k i' j') =
      (overlapHom i j i' j' α β hscale).comp
        (toOverlapRight k 3 (segreIndex (i, j)) (segreIndex (i', j'))) := by
  apply HomogeneousAway.ringHom_ext (grading k 3) (coordinate_mem k 3 (segreIndex (i', j')))
  intro n a ha
  have hhom : a.IsHomogeneous n := by
    simpa only [smul_eq_mul, mul_one] using (MvPolynomial.mem_homogeneousSubmodule _ _).mp ha
  rw [RingHom.comp_apply, RingHom.comp_apply, segreChartHom_mk, toOverlapRight,
    HomogeneousLocalization.awayMap_mk, overlapHom, HomogeneousAway.lift_mk,
    RingHom.comp_apply, map_mul, map_pow, segrePolynomialHom_center, one_pow, mul_one,
    scaled_apply i j i' j' α β hconst hscale a hhom, mul_right_comm, ← mul_pow,
    scaleFactor_mul i j i' j' α β hscale, one_pow, one_mul]

include hscale in
theorem specMap_segreChartSpec_left :
    Spec.map (CommRingCat.ofHom α) ≫ segreChartSpec k i j =
      Spec.map (CommRingCat.ofHom (overlapHom i j i' j' α β hscale)) ≫
        Spec.map (CommRingCat.ofHom
          (toOverlapLeft k 3 (segreIndex (i, j)) (segreIndex (i', j')))) := by
  rw [segreChartSpec, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, overlapHom_left i j i' j' α β hscale]

include hconst hscale in
theorem specMap_segreChartSpec_right :
    Spec.map (CommRingCat.ofHom β) ≫ segreChartSpec k i' j' =
      Spec.map (CommRingCat.ofHom (overlapHom i j i' j' α β hscale)) ≫
        Spec.map (CommRingCat.ofHom
          (toOverlapRight k 3 (segreIndex (i, j)) (segreIndex (i', j')))) := by
  rw [segreChartSpec, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, overlapHom_right i j i' j' α β hconst hscale]

include hscale in
theorem specMap_segreChart_left :
    Spec.map (CommRingCat.ofHom α) ≫ segreChart k i j =
      Spec.map (CommRingCat.ofHom (overlapHom i j i' j' α β hscale)) ≫
        coordinateOverlapMorphism k 3 (segreIndex (i, j)) (segreIndex (i', j')) := by
  rw [segreChart, ← Category.assoc, specMap_segreChartSpec_left i j i' j' α β hscale,
    Category.assoc, SpecMap_toOverlapLeft_chart k 3 (segreIndex (i, j)) (segreIndex (i', j'))]

include hconst hscale in
theorem specMap_segreChart_right :
    Spec.map (CommRingCat.ofHom β) ≫ segreChart k i' j' =
      Spec.map (CommRingCat.ofHom (overlapHom i j i' j' α β hscale)) ≫
        coordinateOverlapMorphism k 3 (segreIndex (i, j)) (segreIndex (i', j')) := by
  rw [segreChart, ← Category.assoc, specMap_segreChartSpec_right i j i' j' α β hconst hscale,
    Category.assoc, SpecMap_toOverlapRight_chart k 3 (segreIndex (i, j)) (segreIndex (i', j'))]

include hconst hscale in
/-- **Compatibility of two Segre chart maps** on a common affine piece `Spec S`. -/
theorem segreChart_compatible :
    Spec.map (CommRingCat.ofHom α) ≫ segreChart k i j =
      Spec.map (CommRingCat.ofHom β) ≫ segreChart k i' j' := by
  rw [specMap_segreChart_left i j i' j' α β hscale,
    specMap_segreChart_right i j i' j' α β hconst hscale]

end Compatibility

end KltDP.Geometry.ProjectiveSegreCover
