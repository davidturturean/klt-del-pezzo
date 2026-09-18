/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.ProjectiveChart

/-!
# The original projective standard chart over any commutative ring

This is the ordinary ring-generality extension of the selected compiled
ProjectiveChart construction. The actual homogeneous-localization rings,
coefficient maps and ratios are unchanged. Its inverse proofs use no field
axiom; the common homogeneous scaling lemma is imported from the original.

For n=1 this is the standard affine chart of the original rank-two free
projectivization, before any relative gluing or literature-source use.
-/

noncomputable section
open scoped BigOperators
open AlgebraicGeometry
universe u
namespace KltDP.Geometry.RelativeProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

abbrev homogeneousRing := MvPolynomial (Fin (n + 1)) R
abbrev affineRing := MvPolynomial (Fin n) R
abbrev grading := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
abbrev coordinate : homogeneousRing R n := MvPolynomial.X 0
abbrev chartRing := HomogeneousLocalization.Away (grading R n) (coordinate R n)
abbrev ambientLocalization := Localization.Away (coordinate R n)

/-- The original coefficient map into degree zero, over a commutative ring. -/
def baseConstants : R →+* grading R n 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C _ a⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)

/-- The actual polynomial substitution defining dehomogenization. -/
def dehomogenizePolynomial : homogeneousRing R n →+* affineRing R n :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)

@[simp] theorem dehomogenizePolynomial_C (r : R) :
    dehomogenizePolynomial R n (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [dehomogenizePolynomial]

@[simp] theorem dehomogenizePolynomial_coordinate :
    dehomogenizePolynomial R n (coordinate R n) = 1 := by
  simp [dehomogenizePolynomial, coordinate]

@[simp] theorem dehomogenizePolynomial_X_succ (i : Fin n) :
    dehomogenizePolynomial R n (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [dehomogenizePolynomial]

/-- Extension to the ordinary localization at `X₀`, whose image is `1`. -/
def dehomogenizeAmbient : ambientLocalization R n →+* affineRing R n :=
  Localization.awayLift (dehomogenizePolynomial R n) (coordinate R n)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

/-- Restriction along the actual inclusion of homogeneous fractions. -/
def dehomogenize : chartRing R n →+* affineRing R n :=
  (dehomogenizeAmbient R n).comp
    (algebraMap (chartRing R n) (ambientLocalization R n))

/-- The original degree-zero base constants in the chart ring. -/
def constants : R →+* chartRing R n :=
  (HomogeneousLocalization.fromZeroRingHom (grading R n)
    (Submonoid.powers (coordinate R n))).comp (baseConstants R n)

/-- A remaining projective coordinate divided by `X₀`, as an actual
homogeneous fraction of equal-degree polynomials. -/
def ratio (i : Fin n) : chartRing R n :=
  HomogeneousLocalization.Away.mk (grading R n)
    (MvPolynomial.isHomogeneous_X R (0 : Fin (n + 1))) 1
    (MvPolynomial.X i.succ)
    (by simpa only [one_smul] using MvPolynomial.isHomogeneous_X R i.succ)

/-- Polynomial evaluation at those actual coordinate fractions. -/
def homogenizeRatios : affineRing R n →+* chartRing R n :=
  MvPolynomial.eval₂Hom (constants R n) (ratio R n)

/-- Dehomogenization of a normalized homogeneous fraction evaluates its
numerator, since every denominator power is sent to one. -/
theorem dehomogenize_mk (m : ℕ) (a : homogeneousRing R n)
    (ha : a ∈ grading R n (m • (1 : ℕ))) :
    dehomogenize R n
        (HomogeneousLocalization.Away.mk (grading R n)
          (MvPolynomial.isHomogeneous_X R (0 : Fin (n + 1))) m a ha) =
      dehomogenizePolynomial R n a := by
  change dehomogenizeAmbient R n
    (Localization.mk a ⟨coordinate R n ^ m, m, rfl⟩) = _
  simpa only [dehomogenizeAmbient, one_pow, mul_one] using
    Localization.awayLift_mk (dehomogenizePolynomial R n) (coordinate R n)
      a (1 : affineRing R n) (by simp) m

theorem constants_val (r : R) :
    algebraMap (chartRing R n) (ambientLocalization R n) (constants R n r) =
      algebraMap (homogeneousRing R n) (ambientLocalization R n) (MvPolynomial.C r) := by
  change Localization.mk (MvPolynomial.C r) ⟨1, _⟩ = _
  rw [Localization.mk_eq_mk']
  change IsLocalization.mk' (ambientLocalization R n) (MvPolynomial.C r) 1 = _
  apply IsLocalization.mk'_one

@[simp] theorem dehomogenize_constants (r : R) :
    dehomogenize R n (constants R n r) = MvPolynomial.C r := by
  change dehomogenizeAmbient R n
    (algebraMap (chartRing R n) (ambientLocalization R n) (constants R n r)) = _
  rw [constants_val]
  simpa only [dehomogenizeAmbient, dehomogenizePolynomial_C] using
    IsLocalization.Away.lift_eq (S := ambientLocalization R n)
      (g := dehomogenizePolynomial R n) (coordinate R n)
      (isUnit_iff_exists_inv.mpr ⟨(1 : affineRing R n), by simp⟩) (MvPolynomial.C r)

@[simp] theorem dehomogenize_ratio (i : Fin n) :
    dehomogenize R n (ratio R n i) = MvPolynomial.X i := by
  rw [ratio, dehomogenize_mk, dehomogenizePolynomial_X_succ]

theorem dehomogenize_comp_homogenizeRatios :
    (dehomogenize R n).comp (homogenizeRatios R n) = RingHom.id (affineRing R n) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [homogenizeRatios]
  · intro i
    simp [homogenizeRatios]

@[simp] theorem dehomogenize_homogenizeRatios (p : affineRing R n) :
    dehomogenize R n (homogenizeRatios R n p) = p :=
  RingHom.congr_fun (dehomogenize_comp_homogenizeRatios R n) p

/-- The existing inverse of `X₀` in the ordinary localization. -/
abbrev inverseCoordinate : ambientLocalization R n :=
  IsLocalization.Away.invSelf (S := ambientLocalization R n) (coordinate R n)

theorem ratio_val (i : Fin n) :
    algebraMap (chartRing R n) (ambientLocalization R n) (ratio R n i) =
      algebraMap (homogeneousRing R n) (ambientLocalization R n) (MvPolynomial.X i.succ) *
        inverseCoordinate R n := by
  change Localization.mk (MvPolynomial.X i.succ)
      ⟨coordinate R n ^ 1, _⟩ = _
  rw [Localization.mk_eq_mk']
  symm
  apply (IsLocalization.eq_mk'_iff_mul_eq).mpr
  change (_ * inverseCoordinate R n) *
    algebraMap (homogeneousRing R n) (ambientLocalization R n) (coordinate R n ^ 1) = _
  rw [pow_one]
  calc
    _ = algebraMap (homogeneousRing R n) (ambientLocalization R n) (MvPolynomial.X i.succ) *
        (algebraMap (homogeneousRing R n) (ambientLocalization R n) (coordinate R n) *
          inverseCoordinate R n) := by ac_rfl
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

/-- Evaluation at ratios is evaluation at all homogeneous coordinates
scaled by the actual inverse of `X₀`. -/
theorem ambient_homogenize_dehomogenizePolynomial :
    ((algebraMap (chartRing R n) (ambientLocalization R n)).comp
        (homogenizeRatios R n)).comp (dehomogenizePolynomial R n) =
      MvPolynomial.eval₂Hom
        ((algebraMap (homogeneousRing R n) (ambientLocalization R n)).comp MvPolynomial.C)
        (fun i ↦ inverseCoordinate R n *
          algebraMap (homogeneousRing R n) (ambientLocalization R n) (MvPolynomial.X i)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa [homogenizeRatios] using constants_val R n r
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [RingHom.comp_apply, dehomogenizePolynomial_coordinate,
        map_one, MvPolynomial.eval₂Hom_X']
      change (1 : ambientLocalization R n) = inverseCoordinate R n *
        algebraMap (homogeneousRing R n) (ambientLocalization R n) (coordinate R n)
      rw [mul_comm, IsLocalization.Away.mul_invSelf]
    · simp only [RingHom.comp_apply, dehomogenizePolynomial_X_succ,
        homogenizeRatios, MvPolynomial.eval₂Hom_X', ratio_val]
      exact mul_comm _ _

theorem homogenize_dehomogenizePolynomial_val {m : ℕ} (a : homogeneousRing R n)
    (ha : a.IsHomogeneous m) :
    algebraMap (chartRing R n) (ambientLocalization R n)
        (homogenizeRatios R n (dehomogenizePolynomial R n a)) =
      inverseCoordinate R n ^ m *
        algebraMap (homogeneousRing R n) (ambientLocalization R n) a := by
  have h := RingHom.congr_fun (ambient_homogenize_dehomogenizePolynomial R n) a
  change _ = MvPolynomial.eval₂ _ _ a at h
  rw [homogeneous_eval₂_scale ha] at h
  calc
    _ = inverseCoordinate R n ^ m *
        MvPolynomial.eval₂
          ((algebraMap (homogeneousRing R n) (ambientLocalization R n)).comp MvPolynomial.C)
          (fun i ↦ algebraMap (homogeneousRing R n) (ambientLocalization R n) (MvPolynomial.X i)) a := h
    _ = _ := by
      congr 1
      exact (MvPolynomial.eval₂_comp_left
        (algebraMap (homogeneousRing R n) (ambientLocalization R n)) MvPolynomial.C
        MvPolynomial.X a).symm.trans
          (congrArg (algebraMap (homogeneousRing R n) (ambientLocalization R n))
            (MvPolynomial.eval₂_eta a))

/-- The other inverse law, checked on every actual normalized homogeneous
fraction and then reflected through the injective localization inclusion. -/
@[simp] theorem homogenizeRatios_dehomogenize (z : chartRing R n) :
    homogenizeRatios R n (dehomogenize R n z) = z := by
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading R n)
    (MvPolynomial.isHomogeneous_X R (0 : Fin (n + 1))) z
  have ha' : a.IsHomogeneous m := by
    simpa only [smul_eq_mul, mul_one] using ha
  apply HomogeneousLocalization.val_injective (𝒜 := grading R n)
    (Submonoid.powers (coordinate R n))
  rw [dehomogenize_mk]
  change algebraMap (chartRing R n) (ambientLocalization R n)
      (homogenizeRatios R n (dehomogenizePolynomial R n a)) =
    Localization.mk a ⟨coordinate R n ^ m, _⟩
  rw [homogenize_dehomogenizePolynomial_val R n a ha', Localization.mk_eq_mk',
    IsLocalization.eq_mk'_iff_mul_eq, map_pow]
  calc
    _ = algebraMap (homogeneousRing R n) (ambientLocalization R n) a *
        (algebraMap (homogeneousRing R n) (ambientLocalization R n) (coordinate R n) ^ m *
          inverseCoordinate R n ^ m) := by ac_rfl
    _ = algebraMap (homogeneousRing R n) (ambientLocalization R n) a *
        (algebraMap (homogeneousRing R n) (ambientLocalization R n) (coordinate R n) *
          inverseCoordinate R n) ^ m := by rw [mul_pow]
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- The actual homogeneous coordinate ring of `X₀ ≠ 0` is the ordinary
polynomial ring in the remaining variables, through the maps above. -/
def coordinateRingEquiv : chartRing R n ≃+* affineRing R n where
  __ := dehomogenize R n
  invFun := homogenizeRatios R n
  left_inv := homogenizeRatios_dehomogenize R n
  right_inv := dehomogenize_homogenizeRatios R n

@[simp] theorem coordinateRingEquiv_constants (r : R) :
    coordinateRingEquiv R n (constants R n r) = MvPolynomial.C r :=
  dehomogenize_constants R n r


end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coordinateRingEquiv
#print axioms KltDP.Geometry.RelativeProjectiveChart.coordinateRingEquiv_constants
