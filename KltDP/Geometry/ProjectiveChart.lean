import KltDP.Geometry.Surface
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Polynomial coordinates on an actual projective chart

On the standard chart `X₀ ≠ 0`, dehomogenization substitutes `X₀ = 1`
and keeps the other coordinates. It extends to the ordinary localization
and restricts to the actual homogeneous-localization ring. The inverse
sends each polynomial variable to the degree-zero fraction `Xᵢ₊₁/X₀`.

The inverse laws use the existing normalized homogeneous-fraction
representatives and the scalar-evaluation identity for homogeneous
polynomials. No coordinate-ring isomorphism is assumed.
-/

noncomputable section

open scoped BigOperators
open AlgebraicGeometry

universe u

namespace KltDP.Geometry

/-- Scalar evaluation of a homogeneous polynomial, proved from its actual
coefficient support. The target need not be a field. -/
theorem homogeneous_eval₂_scale {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d)
    (f : R →+* S) (g : σ → S) (t : S) :
    MvPolynomial.eval₂ f (fun i ↦ t * g i) p =
      t ^ d * MvPolynomial.eval₂ f g p := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmdegree : (∑ i ∈ m.support, m i) = d := by
    change m.degree = d
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hm)
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hmdegree]
  ac_rfl

namespace ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

abbrev homogeneousRing := MvPolynomial (Fin (n + 1)) k
abbrev affineRing := MvPolynomial (Fin n) k
abbrev grading := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
abbrev coordinate : homogeneousRing k n := MvPolynomial.X 0
abbrev chartRing := HomogeneousLocalization.Away (grading k n) (coordinate k n)
abbrev ambientLocalization := Localization.Away (coordinate k n)

/-- The actual polynomial substitution defining dehomogenization. -/
def dehomogenizePolynomial : homogeneousRing k n →+* affineRing k n :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)

@[simp] theorem dehomogenizePolynomial_C (r : k) :
    dehomogenizePolynomial k n (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [dehomogenizePolynomial]

@[simp] theorem dehomogenizePolynomial_coordinate :
    dehomogenizePolynomial k n (coordinate k n) = 1 := by
  simp [dehomogenizePolynomial, coordinate]

@[simp] theorem dehomogenizePolynomial_X_succ (i : Fin n) :
    dehomogenizePolynomial k n (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [dehomogenizePolynomial]

/-- Extension to the ordinary localization at `X₀`, whose image is `1`. -/
def dehomogenizeAmbient : ambientLocalization k n →+* affineRing k n :=
  Localization.awayLift (dehomogenizePolynomial k n) (coordinate k n)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

/-- Restriction along the actual inclusion of homogeneous fractions. -/
def dehomogenize : chartRing k n →+* affineRing k n :=
  (dehomogenizeAmbient k n).comp
    (algebraMap (chartRing k n) (ambientLocalization k n))

/-- The original degree-zero base constants in the chart ring. -/
def constants : k →+* chartRing k n :=
  (HomogeneousLocalization.fromZeroRingHom (grading k n)
    (Submonoid.powers (coordinate k n))).comp (projectiveSpaceConstants k n)

/-- A remaining projective coordinate divided by `X₀`, as an actual
homogeneous fraction of equal-degree polynomials. -/
def ratio (i : Fin n) : chartRing k n :=
  HomogeneousLocalization.Away.mk (grading k n)
    (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 1))) 1
    (MvPolynomial.X i.succ)
    (by simpa only [one_smul] using MvPolynomial.isHomogeneous_X k i.succ)

/-- Polynomial evaluation at those actual coordinate fractions. -/
def homogenizeRatios : affineRing k n →+* chartRing k n :=
  MvPolynomial.eval₂Hom (constants k n) (ratio k n)

/-- Dehomogenization of a normalized homogeneous fraction evaluates its
numerator, since every denominator power is sent to one. -/
theorem dehomogenize_mk (m : ℕ) (a : homogeneousRing k n)
    (ha : a ∈ grading k n (m • (1 : ℕ))) :
    dehomogenize k n
        (HomogeneousLocalization.Away.mk (grading k n)
          (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 1))) m a ha) =
      dehomogenizePolynomial k n a := by
  change dehomogenizeAmbient k n
    (Localization.mk a ⟨coordinate k n ^ m, m, rfl⟩) = _
  simpa only [dehomogenizeAmbient, one_pow, mul_one] using
    Localization.awayLift_mk (dehomogenizePolynomial k n) (coordinate k n)
      a (1 : affineRing k n) (by simp) m

theorem constants_val (r : k) :
    algebraMap (chartRing k n) (ambientLocalization k n) (constants k n r) =
      algebraMap (homogeneousRing k n) (ambientLocalization k n) (MvPolynomial.C r) := by
  change Localization.mk (MvPolynomial.C r) ⟨1, _⟩ = _
  rw [Localization.mk_eq_mk']
  change IsLocalization.mk' (ambientLocalization k n) (MvPolynomial.C r) 1 = _
  apply IsLocalization.mk'_one

@[simp] theorem dehomogenize_constants (r : k) :
    dehomogenize k n (constants k n r) = MvPolynomial.C r := by
  change dehomogenizeAmbient k n
    (algebraMap (chartRing k n) (ambientLocalization k n) (constants k n r)) = _
  rw [constants_val]
  simpa only [dehomogenizeAmbient, dehomogenizePolynomial_C] using
    IsLocalization.Away.lift_eq (S := ambientLocalization k n)
      (g := dehomogenizePolynomial k n) (coordinate k n)
      (isUnit_iff_exists_inv.mpr ⟨(1 : affineRing k n), by simp⟩) (MvPolynomial.C r)

@[simp] theorem dehomogenize_ratio (i : Fin n) :
    dehomogenize k n (ratio k n i) = MvPolynomial.X i := by
  rw [ratio, dehomogenize_mk, dehomogenizePolynomial_X_succ]

theorem dehomogenize_comp_homogenizeRatios :
    (dehomogenize k n).comp (homogenizeRatios k n) = RingHom.id (affineRing k n) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [homogenizeRatios]
  · intro i
    simp [homogenizeRatios]

@[simp] theorem dehomogenize_homogenizeRatios (p : affineRing k n) :
    dehomogenize k n (homogenizeRatios k n p) = p :=
  RingHom.congr_fun (dehomogenize_comp_homogenizeRatios k n) p

/-- The existing inverse of `X₀` in the ordinary localization. -/
abbrev inverseCoordinate : ambientLocalization k n :=
  IsLocalization.Away.invSelf (S := ambientLocalization k n) (coordinate k n)

theorem ratio_val (i : Fin n) :
    algebraMap (chartRing k n) (ambientLocalization k n) (ratio k n i) =
      algebraMap (homogeneousRing k n) (ambientLocalization k n) (MvPolynomial.X i.succ) *
        inverseCoordinate k n := by
  change Localization.mk (MvPolynomial.X i.succ)
      ⟨coordinate k n ^ 1, _⟩ = _
  rw [Localization.mk_eq_mk']
  symm
  apply (IsLocalization.eq_mk'_iff_mul_eq).mpr
  change (_ * inverseCoordinate k n) *
    algebraMap (homogeneousRing k n) (ambientLocalization k n) (coordinate k n ^ 1) = _
  rw [pow_one]
  calc
    _ = algebraMap (homogeneousRing k n) (ambientLocalization k n) (MvPolynomial.X i.succ) *
        (algebraMap (homogeneousRing k n) (ambientLocalization k n) (coordinate k n) *
          inverseCoordinate k n) := by ac_rfl
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

/-- Evaluation at ratios is evaluation at all homogeneous coordinates
scaled by the actual inverse of `X₀`. -/
theorem ambient_homogenize_dehomogenizePolynomial :
    ((algebraMap (chartRing k n) (ambientLocalization k n)).comp
        (homogenizeRatios k n)).comp (dehomogenizePolynomial k n) =
      MvPolynomial.eval₂Hom
        ((algebraMap (homogeneousRing k n) (ambientLocalization k n)).comp MvPolynomial.C)
        (fun i ↦ inverseCoordinate k n *
          algebraMap (homogeneousRing k n) (ambientLocalization k n) (MvPolynomial.X i)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa [homogenizeRatios] using constants_val k n r
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [RingHom.comp_apply, dehomogenizePolynomial_coordinate,
        map_one, MvPolynomial.eval₂Hom_X']
      change (1 : ambientLocalization k n) = inverseCoordinate k n *
        algebraMap (homogeneousRing k n) (ambientLocalization k n) (coordinate k n)
      rw [mul_comm, IsLocalization.Away.mul_invSelf]
    · simp only [RingHom.comp_apply, dehomogenizePolynomial_X_succ,
        homogenizeRatios, MvPolynomial.eval₂Hom_X', ratio_val]
      exact mul_comm _ _

theorem homogenize_dehomogenizePolynomial_val {m : ℕ} (a : homogeneousRing k n)
    (ha : a.IsHomogeneous m) :
    algebraMap (chartRing k n) (ambientLocalization k n)
        (homogenizeRatios k n (dehomogenizePolynomial k n a)) =
      inverseCoordinate k n ^ m *
        algebraMap (homogeneousRing k n) (ambientLocalization k n) a := by
  have h := RingHom.congr_fun (ambient_homogenize_dehomogenizePolynomial k n) a
  change _ = MvPolynomial.eval₂ _ _ a at h
  rw [homogeneous_eval₂_scale ha] at h
  calc
    _ = inverseCoordinate k n ^ m *
        MvPolynomial.eval₂
          ((algebraMap (homogeneousRing k n) (ambientLocalization k n)).comp MvPolynomial.C)
          (fun i ↦ algebraMap (homogeneousRing k n) (ambientLocalization k n) (MvPolynomial.X i)) a := h
    _ = _ := by
      congr 1
      exact (MvPolynomial.eval₂_comp_left
        (algebraMap (homogeneousRing k n) (ambientLocalization k n)) MvPolynomial.C
        MvPolynomial.X a).symm.trans
          (congrArg (algebraMap (homogeneousRing k n) (ambientLocalization k n))
            (MvPolynomial.eval₂_eta a))

/-- The other inverse law, checked on every actual normalized homogeneous
fraction and then reflected through the injective localization inclusion. -/
@[simp] theorem homogenizeRatios_dehomogenize (z : chartRing k n) :
    homogenizeRatios k n (dehomogenize k n z) = z := by
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading k n)
    (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 1))) z
  have ha' : a.IsHomogeneous m := by
    simpa only [smul_eq_mul, mul_one] using ha
  apply HomogeneousLocalization.val_injective (𝒜 := grading k n)
    (Submonoid.powers (coordinate k n))
  rw [dehomogenize_mk]
  change algebraMap (chartRing k n) (ambientLocalization k n)
      (homogenizeRatios k n (dehomogenizePolynomial k n a)) =
    Localization.mk a ⟨coordinate k n ^ m, _⟩
  rw [homogenize_dehomogenizePolynomial_val k n a ha', Localization.mk_eq_mk',
    IsLocalization.eq_mk'_iff_mul_eq, map_pow]
  calc
    _ = algebraMap (homogeneousRing k n) (ambientLocalization k n) a *
        (algebraMap (homogeneousRing k n) (ambientLocalization k n) (coordinate k n) ^ m *
          inverseCoordinate k n ^ m) := by ac_rfl
    _ = algebraMap (homogeneousRing k n) (ambientLocalization k n) a *
        (algebraMap (homogeneousRing k n) (ambientLocalization k n) (coordinate k n) *
          inverseCoordinate k n) ^ m := by rw [mul_pow]
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- The actual homogeneous coordinate ring of `X₀ ≠ 0` is the ordinary
polynomial ring in the remaining variables, through the maps above. -/
def coordinateRingEquiv : chartRing k n ≃+* affineRing k n where
  __ := dehomogenize k n
  invFun := homogenizeRatios k n
  left_inv := homogenizeRatios_dehomogenize k n
  right_inv := dehomogenize_homogenizeRatios k n

@[simp] theorem coordinateRingEquiv_constants (r : k) :
    coordinateRingEquiv k n (constants k n r) = MvPolynomial.C r :=
  dehomogenize_constants k n r

end ProjectiveChart

end KltDP.Geometry
