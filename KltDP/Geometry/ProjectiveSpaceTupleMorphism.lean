import KltDP.Geometry.ProjectiveSpaceChartRange
import KltDP.Geometry.SpecHomRingHom

/-!
# Morphisms `Spec R ⟶ projectiveSpace k n` from a normalised coordinate tuple

A ring `R` with constants `c : k →+* R`, a tuple `r : Fin (n+1) → R` and an index `m` with `r m = 1`
("homogeneous coordinates normalised at `z_m`") determine the ring map
`tupleChartHom : A_{(z_m)} →+* R`, `z_i / z_m ↦ r i` (the lift of the substitution `z_i ↦ r i` along
the pinned `HomogeneousLocalization.Away`, `HomogeneousAway.lift`), hence the morphism
`tupleMorphism : Spec R ⟶ P^n` landing in the chart `D(z_m)`. This is the generic form of the
BRIEF10 Segre chart maps (`segreChart i j` is the case `r = segreImage i j`).

* `tupleMorphism_structure`: the morphism is over `k` (`≫ projectiveSpaceToSpec k n = Spec.map c`);
* `tupleMorphism_base_mem_range_iff`: its image at `x` lies in the chart `D(z_i)` iff `r i ∉ x`;
* `tupleSpec_isClosedImmersion`: the map into the chart is a closed immersion when `tupleChartHom`
  is surjective (pinned `IsClosedImmersion.spec_of_surjective`);
* `specMap_tupleMorphism`: naturality in `R` (`Spec.map α ≫ tupleMorphism c r = tupleMorphism (α ∘ c) (α ∘ r)`);
* `tupleMorphism_eq_of_scale`: two tuples in the same ring normalised at `m`, `m'` and related by the
  scaling identity `r i = r m' * r' i` give the same morphism (both factor through the overlap chart
  `D(z_m z_{m'})`; the generic form of the BRIEF10 `segreChart_compatible`);
* `comp_tupleMorphism`: for `f : W ⟶ Spec R`, `f ≫ tupleMorphism c r` is the tuple morphism of the
  pulled-back functions `f^* r ∈ Γ(W, ⊤)` after `W.toSpecΓ` — the form in which compatibility on an
  abstract overlap `W` is checked.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

section Basic

variable {k : Type u} [Field k] (n : ℕ) {R : Type u} [CommRing R] (c : k →+* R)
  (r : Fin (n + 1) → R)

/-- The substitution `z_i ↦ r i`, constants through `c`. -/
def tuplePolynomialHom : homogeneousRing k n →+* R := MvPolynomial.eval₂Hom c r

@[simp] theorem tuplePolynomialHom_C (a : k) :
    tuplePolynomialHom n c r (MvPolynomial.C a) = c a :=
  MvPolynomial.eval₂Hom_C _ _ a

@[simp] theorem tuplePolynomialHom_X (i : Fin (n + 1)) :
    tuplePolynomialHom n c r (MvPolynomial.X i) = r i :=
  MvPolynomial.eval₂Hom_X' _ _ i

variable (m : Fin (n + 1)) (hm : r m = 1)

/-- The chart ring map `A_{(z_m)} →+* R`, `z_i / z_m ↦ r i`. -/
def tupleChartHom : coordinateChartRing k n m →+* R :=
  HomogeneousAway.lift (grading k n) (tuplePolynomialHom n c r) 1
    (by rw [tuplePolynomialHom_X, hm, mul_one])

theorem tupleChartHom_mk (d : ℕ) (a : homogeneousRing k n) (ha : a ∈ grading k n (d • 1)) :
    tupleChartHom n c r m hm
        (HomogeneousLocalization.Away.mk (grading k n) (coordinate_mem k n m) d a ha) =
      tuplePolynomialHom n c r a := by
  rw [tupleChartHom, HomogeneousAway.lift_mk, one_pow, mul_one]

@[simp] theorem tupleChartHom_constants (a : k) :
    tupleChartHom n c r m hm (coordinateChartConstants k n m a) = c a := by
  rw [tupleChartHom, coordinateChartConstants, RingHom.comp_apply,
    HomogeneousAway.lift_fromZeroRingHom]
  exact tuplePolynomialHom_C n c r a

@[simp] theorem tupleChartHom_chartFraction (i : Fin (n + 1)) :
    tupleChartHom n c r m hm (chartFraction k n m i) = r i := by
  rw [chartFraction_eq, tupleChartHom_mk, tuplePolynomialHom_X]

/-- The map `Spec R ⟶ Spec (A_{(z_m)})` of the tuple. -/
def tupleSpec : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (coordinateChartRing k n m)) :=
  Spec.map (CommRingCat.ofHom (tupleChartHom n c r m hm))

/-- The morphism `Spec R ⟶ P^n` with homogeneous coordinates `r`, normalised at `z_m`. -/
def tupleMorphism : Spec (CommRingCat.of R) ⟶ projectiveSpace k n :=
  tupleSpec n c r m hm ≫ coordinateChartMorphism k n m

/-- The tuple morphism is over `k`. -/
theorem tupleMorphism_structure :
    tupleMorphism n c r m hm ≫ projectiveSpaceToSpec k n = Spec.map (CommRingCat.ofHom c) := by
  rw [tupleMorphism, Category.assoc, coordinateChartMorphism_over_base, tupleSpec, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun a => tupleChartHom_constants n c r m hm a)

/-- The map into the chart is a closed immersion when the chart ring map is surjective. -/
theorem tupleSpec_isClosedImmersion (h : Function.Surjective (tupleChartHom n c r m hm)) :
    IsClosedImmersion (tupleSpec n c r m hm) :=
  IsClosedImmersion.spec_of_surjective _ h

/-- The image of `x` lies in the chart `D(z_i)` iff `r i` is invertible at `x`. -/
theorem tupleMorphism_base_mem_range_iff (x : Spec (CommRingCat.of R)) (i : Fin (n + 1)) :
    (tupleMorphism n c r m hm).base x ∈ Set.range (coordinateChartMorphism k n i).base ↔
      x ∈ PrimeSpectrum.basicOpen (r i) := by
  rw [tupleMorphism, Scheme.comp_base_apply, coordinateChartMorphism_mem_range_iff, tupleSpec,
    specMap_base_mem_basicOpen_iff, tupleChartHom_chartFraction]

section Naturality

variable {S : Type u} [CommRing S] (α : R →+* S)

theorem tupleChartHom_comp :
    α.comp (tupleChartHom n c r m hm) =
      tupleChartHom n (α.comp c) (α ∘ r) m
        (by simp only [Function.comp_apply, hm, map_one]) := by
  apply HomogeneousAway.ringHom_ext (grading k n) (coordinate_mem k n m)
  intro d a ha
  rw [RingHom.comp_apply, tupleChartHom_mk, tupleChartHom_mk]
  exact MvPolynomial.eval₂_comp_left α c r a

/-- Naturality of the tuple morphism in the ring. -/
theorem specMap_tupleMorphism :
    Spec.map (CommRingCat.ofHom α) ≫ tupleMorphism n c r m hm =
      tupleMorphism n (α.comp c) (α ∘ r) m
        (by simp only [Function.comp_apply, hm, map_one]) := by
  rw [tupleMorphism, tupleMorphism, tupleSpec, tupleSpec, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, tupleChartHom_comp]

/-- A morphism `f : W ⟶ Spec R` followed by the tuple morphism is the tuple morphism of the
pulled-back functions, after `W.toSpecΓ`. -/
theorem comp_tupleMorphism {W : Scheme.{u}} (f : W ⟶ Spec (CommRingCat.of R)) :
    f ≫ tupleMorphism n c r m hm =
      W.toSpecΓ ≫ tupleMorphism n ((specHomRingHom f).hom.comp c) ((specHomRingHom f).hom ∘ r) m
        (by simp only [Function.comp_apply, hm, map_one]) := by
  have h := specMap_tupleMorphism n c r m hm (specHomRingHom f).hom
  rw [CommRingCat.ofHom_hom] at h
  rw [← h, ← Category.assoc, ← specHom_eq_toSpecΓ f]

end Naturality

end Basic

section Compatibility

variable {k : Type u} [Field k] {n : ℕ} {S : Type u} [CommRing S] (c : k →+* S) (r r' : Fin (n + 1) → S)
  (m m' : Fin (n + 1)) (hm : r m = 1) (hm' : r' m' = 1) (hscale : ∀ i, r i = r m' * r' i)

include hm hscale in
theorem scale_mul : r m' * r' m = 1 := by
  rw [← hscale m, hm]

include hm hscale in
/-- The common map out of the overlap chart ring `A_{(z_m z_{m'})}`. -/
def overlapTupleHom : coordinateOverlapRing k n m m' →+* S :=
  HomogeneousAway.lift (grading k n) (tuplePolynomialHom n c r) (r' m)
    (by
      rw [map_mul, tuplePolynomialHom_X, tuplePolynomialHom_X, hm, one_mul]
      exact scale_mul r r' m m' hm hscale)

include hm hscale in
theorem overlapTupleHom_left :
    tupleChartHom n c r m hm =
      (overlapTupleHom c r r' m m' hm hscale).comp (toOverlapLeft k n m m') := by
  apply HomogeneousAway.ringHom_ext (grading k n) (coordinate_mem k n m)
  intro d a ha
  rw [tupleChartHom_mk, RingHom.comp_apply, toOverlapLeft, HomogeneousLocalization.awayMap_mk,
    overlapTupleHom, HomogeneousAway.lift_mk, map_mul, map_pow, tuplePolynomialHom_X, mul_assoc,
    ← mul_pow, scale_mul r r' m m' hm hscale, one_pow, mul_one]

include hm hm' hscale in
theorem overlapTupleHom_right :
    tupleChartHom n c r' m' hm' =
      (overlapTupleHom c r r' m m' hm hscale).comp (toOverlapRight k n m m') := by
  apply HomogeneousAway.ringHom_ext (grading k n) (coordinate_mem k n m')
  intro d a ha
  have hhom : a.IsHomogeneous d := by
    simpa only [smul_eq_mul, mul_one] using (MvPolynomial.mem_homogeneousSubmodule _ _).mp ha
  have hP : tuplePolynomialHom n c r a = r m' ^ d * tuplePolynomialHom n c r' a := by
    have h1 : tuplePolynomialHom n c r = MvPolynomial.eval₂Hom c (fun i => r m' * r' i) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp
      · intro i
        rw [tuplePolynomialHom_X, MvPolynomial.eval₂Hom_X']
        exact hscale i
    rw [h1]
    exact homogeneous_eval₂_scale hhom c r' (r m')
  rw [tupleChartHom_mk, RingHom.comp_apply, toOverlapRight, HomogeneousLocalization.awayMap_mk,
    overlapTupleHom, HomogeneousAway.lift_mk, map_mul, map_pow, tuplePolynomialHom_X, hm, one_pow,
    mul_one, hP, mul_right_comm, ← mul_pow, scale_mul r r' m m' hm hscale, one_pow, one_mul]

include hm hscale in
theorem tupleSpec_eq_overlap_left :
    tupleSpec n c r m hm =
      Spec.map (CommRingCat.ofHom (overlapTupleHom c r r' m m' hm hscale)) ≫
        Spec.map (CommRingCat.ofHom (toOverlapLeft k n m m')) := by
  rw [tupleSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, overlapTupleHom_left c r r' m m' hm hscale]

include hm hm' hscale in
theorem tupleSpec_eq_overlap_right :
    tupleSpec n c r' m' hm' =
      Spec.map (CommRingCat.ofHom (overlapTupleHom c r r' m m' hm hscale)) ≫
        Spec.map (CommRingCat.ofHom (toOverlapRight k n m m')) := by
  rw [tupleSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    overlapTupleHom_right c r r' m m' hm hm' hscale]

include hm hscale in
theorem tupleMorphism_eq_overlap_left :
    tupleMorphism n c r m hm =
      Spec.map (CommRingCat.ofHom (overlapTupleHom c r r' m m' hm hscale)) ≫
        coordinateOverlapMorphism k n m m' := by
  rw [tupleMorphism, tupleSpec_eq_overlap_left c r r' m m' hm hscale, Category.assoc,
    SpecMap_toOverlapLeft_chart k n m m']

include hm hm' hscale in
theorem tupleMorphism_eq_overlap_right :
    tupleMorphism n c r' m' hm' =
      Spec.map (CommRingCat.ofHom (overlapTupleHom c r r' m m' hm hscale)) ≫
        coordinateOverlapMorphism k n m m' := by
  rw [tupleMorphism, tupleSpec_eq_overlap_right c r r' m m' hm hm' hscale, Category.assoc,
    SpecMap_toOverlapRight_chart k n m m']

include hscale in
/-- **Two normalised tuples related by the scaling identity give the same morphism.** -/
theorem tupleMorphism_eq_of_scale :
    tupleMorphism n c r m hm = tupleMorphism n c r' m' hm' := by
  rw [tupleMorphism_eq_overlap_left c r r' m m' hm hscale,
    tupleMorphism_eq_overlap_right c r r' m m' hm hm' hscale]

end Compatibility

section TwoRings

variable {k : Type u} [Field k] {n : ℕ} {R R' S : Type u} [CommRing R] [CommRing R'] [CommRing S]
  (c : k →+* R) (c' : k →+* R') (r : Fin (n + 1) → R) (r' : Fin (n + 1) → R')
  (m m' : Fin (n + 1)) (hm : r m = 1) (hm' : r' m' = 1) (α : R →+* S) (β : R' →+* S)

/-- **Compatibility of two tuple morphisms on a common affine piece `Spec S`**: constants agree and
`α (r i) = α (r m') * β (r' i)` for all `i`. -/
theorem tupleMorphism_compatible (hconst : α.comp c = β.comp c')
    (hscale : ∀ i, α (r i) = α (r m') * β (r' i)) :
    Spec.map (CommRingCat.ofHom α) ≫ tupleMorphism n c r m hm =
      Spec.map (CommRingCat.ofHom β) ≫ tupleMorphism n c' r' m' hm' := by
  rw [specMap_tupleMorphism, specMap_tupleMorphism]
  have h := tupleMorphism_eq_of_scale (α.comp c) (α ∘ r) (β ∘ r') m m'
    (by simp only [Function.comp_apply, hm, map_one])
    (by simp only [Function.comp_apply, hm', map_one]) hscale
  rw [h, hconst]

end TwoRings

end KltDP.Geometry.ProjectiveChart
