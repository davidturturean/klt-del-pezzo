import KltDP.Geometry.ProjectiveSpaceTupleMorphism

/-!
# Functions on the charts of `projectiveSpace k n` and their transition on overlaps

* `mk_eq_eval_chartFraction`: in the chart ring `A_{(z_i)}` the fraction `p / z_i^d` of a homogeneous
  polynomial `p` of degree `d` is the polynomial `p` evaluated at the fractions `z_a / z_i`; hence
  every element of the chart ring is a polynomial in the fractions (`exists_eval_chartFraction`).
* On the overlap ring `A_{(z_i z_j)}`: `z_a/z_i = (z_j/z_i)(z_a/z_j)`, `(z_j/z_i)(z_i/z_j) = 1`, and the
  constants of the two charts agree (`toOverlapLeft_chartFraction_eq`, `toOverlapLeft_mul_toOverlapRight`,
  `toOverlapLeft_constants`).
* **Chart transition for maps into two charts**: for `h₀ : V ⟶ Spec A_{(z_i)}`, `h₁ : V ⟶ Spec A_{(z_j)}`
  with `h₀ ≫ chart i = h₁ ≫ chart j`, the pulled-back fractions satisfy
  `h₀^*(z_a/z_i) = h₀^*(z_j/z_i) · h₁^*(z_a/z_j)` and `h₀^*(z_j/z_i) · h₁^*(z_i/z_j) = 1`, and constants
  agree (`chart_relation_mul`, `chart_relation_inv`, `chart_relation_constants`) — the `P^n` form of the
  BRIEF10 `chart_function_relation` for `P¹`, through the pinned `Proj.pullbackAwayιIso`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-! ## Fractions are polynomials in the coordinate fractions -/

theorem chartFraction_val (i a : Fin (n + 1)) :
    (chartFraction k n i a).val =
      Localization.mk (MvPolynomial.X a) ⟨(MvPolynomial.X i : homogeneousRing k n) ^ 1,
        Submonoid.pow_mem _ (Submonoid.mem_powers _) 1⟩ := by
  rw [chartFraction_eq, HomogeneousLocalization.Away.val_mk]

theorem coordinateChartConstants_val (i : Fin (n + 1)) (r : k) :
    (coordinateChartConstants k n i r).val =
      algebraMap (homogeneousRing k n) (Localization.Away (MvPolynomial.X i : homogeneousRing k n))
        (MvPolynomial.C r) := by
  change Localization.mk (MvPolynomial.C r) 1 = _
  exact Localization.mk_one_eq_algebraMap _

/-- **`p / z_i^d = p(z_a / z_i)`** for `p` homogeneous of degree `d`. -/
theorem mk_eq_eval_chartFraction (i : Fin (n + 1)) (d : ℕ) (p : homogeneousRing k n)
    (hp : p ∈ grading k n (d • 1)) :
    HomogeneousLocalization.Away.mk (grading k n) (coordinate_mem k n i) d p hp =
      MvPolynomial.eval₂ (coordinateChartConstants k n i) (chartFraction k n i) p := by
  have hhom : p.IsHomogeneous d := by
    simpa only [smul_eq_mul, mul_one] using (MvPolynomial.mem_homogeneousSubmodule _ _).mp hp
  apply HomogeneousLocalization.val_injective
  set φ := algebraMap (coordinateChartRing k n i)
    (Localization.Away (MvPolynomial.X i : homogeneousRing k n)) with hφ
  have hval : ∀ y : coordinateChartRing k n i, y.val = φ y := fun y => rfl
  set t : Localization.Away (MvPolynomial.X i : homogeneousRing k n) :=
    Localization.mk 1 ⟨(MvPolynomial.X i : homogeneousRing k n) ^ 1,
      Submonoid.pow_mem _ (Submonoid.mem_powers _) 1⟩ with ht
  have hfrac : ∀ a, φ (chartFraction k n i a) =
      t * (algebraMap (homogeneousRing k n)
        (Localization.Away (MvPolynomial.X i : homogeneousRing k n)) ∘ MvPolynomial.X) a := by
    intro a
    rw [← hval, chartFraction_val, ht, Function.comp_apply, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, one_mul, mul_one]
  have hconst : ∀ r : k, φ (coordinateChartConstants k n i r) =
      algebraMap (homogeneousRing k n) _ (MvPolynomial.C r) := fun r => by
    rw [← hval, coordinateChartConstants_val]
  have h1 : (φ.comp (coordinateChartConstants k n i)) =
      (algebraMap (homogeneousRing k n)
        (Localization.Away (MvPolynomial.X i : homogeneousRing k n))).comp MvPolynomial.C := by
    ext r
    exact hconst r
  have h2 : (φ ∘ chartFraction k n i) =
      fun a => t * (algebraMap (homogeneousRing k n)
        (Localization.Away (MvPolynomial.X i : homogeneousRing k n)) ∘ MvPolynomial.X) a := by
    funext a
    exact hfrac a
  have h3 : MvPolynomial.eval₂ ((algebraMap (homogeneousRing k n)
        (Localization.Away (MvPolynomial.X i : homogeneousRing k n))).comp MvPolynomial.C)
      (algebraMap (homogeneousRing k n)
        (Localization.Away (MvPolynomial.X i : homogeneousRing k n)) ∘ MvPolynomial.X) p =
      algebraMap (homogeneousRing k n)
        (Localization.Away (MvPolynomial.X i : homogeneousRing k n)) p := by
    rw [← MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eta]
  rw [HomogeneousLocalization.Away.val_mk, hval, MvPolynomial.eval₂_comp_left, h1, h2,
    homogeneous_eval₂_scale hhom, h3, ← Localization.mk_one_eq_algebraMap, ht, Localization.mk_pow,
    Localization.mk_mul, one_pow, one_mul, mul_one]
  congr 1
  exact Subtype.ext (by simp [pow_one])

/-- Every element of the chart ring is a polynomial in the coordinate fractions. -/
theorem exists_eval_chartFraction (i : Fin (n + 1)) (y : coordinateChartRing k n i) :
    ∃ p : homogeneousRing k n,
      y = MvPolynomial.eval₂ (coordinateChartConstants k n i) (chartFraction k n i) p := by
  obtain ⟨d, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading k n) (coordinate_mem k n i) y
  exact ⟨p, mk_eq_eval_chartFraction k n i d p hp⟩

/-! ## Identities on the overlap ring -/

theorem toOverlapLeft_chartFraction (i j a : Fin (n + 1)) :
    toOverlapLeft k n i j (chartFraction k n i a) =
      HomogeneousLocalization.Away.mk (grading k n) (coordinate_mul_mem k n i j) 1
        (MvPolynomial.X a * MvPolynomial.X j)
        (by simpa only [one_smul] using
          SetLike.mul_mem_graded (coordinate_mem k n a) (coordinate_mem k n j)) := by
  rw [chartFraction_eq, toOverlapLeft, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk]
  simp only [pow_one]

theorem toOverlapRight_chartFraction (i j a : Fin (n + 1)) :
    toOverlapRight k n i j (chartFraction k n j a) =
      HomogeneousLocalization.Away.mk (grading k n) (coordinate_mul_mem k n i j) 1
        (MvPolynomial.X a * MvPolynomial.X i)
        (by simpa only [one_smul] using
          SetLike.mul_mem_graded (coordinate_mem k n a) (coordinate_mem k n i)) := by
  rw [chartFraction_eq, toOverlapRight, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk]
  simp only [pow_one]

/-- `z_a/z_i = (z_j/z_i) · (z_a/z_j)` on the overlap. -/
theorem toOverlapLeft_chartFraction_eq (i j a : Fin (n + 1)) :
    toOverlapLeft k n i j (chartFraction k n i a) =
      toOverlapLeft k n i j (chartFraction k n i j) * toOverlapRight k n i j (chartFraction k n j a) := by
  rw [toOverlapLeft_chartFraction, toOverlapLeft_chartFraction, toOverlapRight_chartFraction,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, pow_one, OneMemClass.coe_one, one_mul]
  ring

/-- `(z_j/z_i) · (z_i/z_j) = 1` on the overlap. -/
theorem toOverlapLeft_mul_toOverlapRight (i j : Fin (n + 1)) :
    toOverlapLeft k n i j (chartFraction k n i j) * toOverlapRight k n i j (chartFraction k n j i) = 1 := by
  rw [toOverlapLeft_chartFraction, toOverlapRight_chartFraction,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one, Localization.mk_mul, ← Localization.mk_one,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, pow_one, OneMemClass.coe_one, one_mul, mul_one]
  ring

/-- Constants agree on the overlap. -/
theorem toOverlapLeft_constants (i j : Fin (n + 1)) (r : k) :
    toOverlapLeft k n i j (coordinateChartConstants k n i r) =
      toOverlapRight k n i j (coordinateChartConstants k n j r) := by
  rw [coordinateChartConstants, coordinateChartConstants, RingHom.comp_apply, RingHom.comp_apply,
    toOverlapLeft, toOverlapRight, HomogeneousLocalization.awayMap_fromZeroRingHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom]

/-! ## Chart transition for two maps into charts -/

section Transition

variable {k n} {V : Scheme.{u}} (i j : Fin (n + 1))
  (h₀ : V ⟶ Spec (CommRingCat.of (coordinateChartRing k n i)))
  (h₁ : V ⟶ Spec (CommRingCat.of (coordinateChartRing k n j)))
  (h : h₀ ≫ coordinateChartMorphism k n i = h₁ ≫ coordinateChartMorphism k n j)

/-- The map of `V` to the overlap chart. -/
def overlapLift : V ⟶ Spec (CommRingCat.of (coordinateOverlapRing k n i j)) :=
  pullback.lift h₀ h₁ h ≫ (coordinateOverlapIso k n i j).hom

theorem overlapLift_left :
    overlapLift i j h₀ h₁ h ≫ Spec.map (CommRingCat.ofHom (toOverlapLeft k n i j)) = h₀ := by
  rw [overlapLift, Category.assoc, ← coordinateOverlapIso_inv_fst, Iso.hom_inv_id_assoc,
    pullback.lift_fst]

theorem overlapLift_right :
    overlapLift i j h₀ h₁ h ≫ Spec.map (CommRingCat.ofHom (toOverlapRight k n i j)) = h₁ := by
  rw [overlapLift, Category.assoc, ← coordinateOverlapIso_inv_snd, Iso.hom_inv_id_assoc,
    pullback.lift_snd]

theorem specHomRingHom_left :
    (specHomRingHom h₀).hom =
      (specHomRingHom (overlapLift i j h₀ h₁ h)).hom.comp (toOverlapLeft k n i j) := by
  have e := congrArg specHomRingHom (overlapLift_left i j h₀ h₁ h)
  rw [specHomRingHom_comp_specMap] at e
  rw [← e]
  rfl

theorem specHomRingHom_right :
    (specHomRingHom h₁).hom =
      (specHomRingHom (overlapLift i j h₀ h₁ h)).hom.comp (toOverlapRight k n i j) := by
  have e := congrArg specHomRingHom (overlapLift_right i j h₀ h₁ h)
  rw [specHomRingHom_comp_specMap] at e
  rw [← e]
  rfl

include h in
/-- **`h₀^*(z_a/z_i) = h₀^*(z_j/z_i) · h₁^*(z_a/z_j)`.** -/
theorem chart_relation_mul (a : Fin (n + 1)) :
    (specHomRingHom h₀).hom (chartFraction k n i a) =
      (specHomRingHom h₀).hom (chartFraction k n i j) *
        (specHomRingHom h₁).hom (chartFraction k n j a) := by
  rw [specHomRingHom_left i j h₀ h₁ h, specHomRingHom_right i j h₀ h₁ h, RingHom.comp_apply,
    RingHom.comp_apply, RingHom.comp_apply, ← map_mul, toOverlapLeft_chartFraction_eq]

include h in
/-- **`h₀^*(z_j/z_i) · h₁^*(z_i/z_j) = 1`.** -/
theorem chart_relation_inv :
    (specHomRingHom h₀).hom (chartFraction k n i j) *
      (specHomRingHom h₁).hom (chartFraction k n j i) = 1 := by
  rw [specHomRingHom_left i j h₀ h₁ h, specHomRingHom_right i j h₀ h₁ h, RingHom.comp_apply,
    RingHom.comp_apply, ← map_mul, toOverlapLeft_mul_toOverlapRight, map_one]

include h in
/-- Constants agree. -/
theorem chart_relation_constants :
    (specHomRingHom h₀).hom.comp (coordinateChartConstants k n i) =
      (specHomRingHom h₁).hom.comp (coordinateChartConstants k n j) := by
  rw [specHomRingHom_left i j h₀ h₁ h, specHomRingHom_right i j h₀ h₁ h, RingHom.comp_assoc,
    RingHom.comp_assoc]
  congr 1
  exact RingHom.ext fun r => toOverlapLeft_constants k n i j r

end Transition

end KltDP.Geometry.ProjectiveChart
