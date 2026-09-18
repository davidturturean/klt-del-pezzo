import KltDP.Geometry.QAmpleWeilDivisor
import KltDP.Geometry.NormalPicardWeilClassInjective
import KltDP.Geometry.PrimeCurveExistence
import KltDP.Geometry.AmpleCurveRestrictionPositive
import KltDP.Geometry.PrimeCurveIntersectionNumber

/-!
# The sign forced by an ample anticanonical numerator

The original integral Weil-class relation lifts to the actual Picard
group after multiplying by the positive Cartier denominator. A prime
curve exists by the surface dimension, and both actual ample lines have
positive restriction degree on that curve. No curve or positivity witness
is an additional input.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

private theorem canonical_multiple_eq {G : Type*} [AddCommGroup G]
    (k a b : G) (c d n : ℤ)
    (h : c • k + d • a = 0) (hb : b = n • (-k)) :
    c • b = (n * d) • a := by
  have hneg : c • (-k) = d • a := by
    simpa only [zsmul_neg, neg_neg] using
      congrArg (fun z : G => -z) (eq_neg_of_add_eq_zero_left h)
  calc
    c • b = c • (n • (-k)) := congrArg (fun z : G => c • z) hb
    _ = n • (c • (-k)) :=
      (mul_zsmul' (-k) n c).symm.trans (mul_zsmul (-k) n c)
    _ = n • (d • a) := congrArg (fun z : G => n • z) hneg
    _ = (n * d) • a := (mul_zsmul a n d).symm

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- An ample anticanonical numerator forces the ample coefficient in the
original integral canonical relation to be strictly positive. -/
theorem canonical_coefficient_pos_of_neg_qAmple
    (D : X.WeilDivisor) (L : InvertibleSheaf X.toScheme)
    (c d : ℤ) (hc : 0 < c) (hL : AmpleSerre.IsAmple L)
    (hrel : c • X.weilClassMap D +
      d • X.picardToWeilClassHom (Additive.ofMul L.toPic) = 0)
    (hQ : X.QAmple (-rationalizeWeilDivisor X D)) : 0 < d := by
  obtain ⟨N, hN, B, hB, hBample⟩ := hQ
  have hBW : X.cartierToWeilHom B = N • (-D) := by
    apply rationalizeWeilDivisor_injective
    simpa only [map_nsmul, map_neg] using hB
  have hBclass : X.picardToWeilClassHom (cartierPicardHom X.toScheme B) =
      (N : ℤ) • (-X.weilClassMap D) := by
    rw [X.picardToWeilClassHom_cartierPicardHom, hBW,
      map_nsmul, map_neg, natCast_zsmul]
  have hclass := canonical_multiple_eq
    (X.weilClassMap D)
    (X.picardToWeilClassHom (Additive.ofMul L.toPic))
    (X.picardToWeilClassHom (cartierPicardHom X.toScheme B))
    c d (N : ℤ) hrel hBclass
  have hPic : c • cartierPicardHom X.toScheme B =
      ((N : ℤ) * d) • Additive.ofMul L.toPic := by
    apply X.picardToWeilClassHom_injective
    simpa only [map_zsmul] using hclass
  obtain ⟨C⟩ := X.primeCurve_nonempty
  have hdeg := congrArg (X.picardRestrictionDegreeHom C) hPic
  have hLB : X.picardRestrictionDegreeHom C (Additive.ofMul L.toPic) =
      C.restrictionDegree L := by
    rw [picardRestrictionDegreeHom_apply, toMul_ofMul,
      C.picardRestrictionDegree_toPic]
  have hdegrees :
      c * C.restrictionDegree (cartierDivisorInvertibleSheaf X.toScheme B) =
        ((N : ℤ) * d) * C.restrictionDegree L := by
    simpa only [map_zsmul, zsmul_eq_mul,
      C.picardRestrictionDegreeHom_cartierPicardHom,
      C.intersectionNumber_eq_restrictionDegree, hLB] using hdeg
  have hdegB := AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple
    X (cartierDivisorInvertibleSheaf X.toScheme B) hBample C
  have hdegL := AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple X L hL C
  have hprod : 0 < ((N : ℤ) * d) * C.restrictionDegree L :=
    hdegrees ▸ mul_pos hc hdegB
  have hNd : 0 < (N : ℤ) * d := (mul_pos_iff_of_pos_right hdegL).mp hprod
  have hNZ : (0 : ℤ) < N := by exact_mod_cast hN
  exact (mul_pos_iff_of_pos_left hNZ).mp hNd

end KltDP.Geometry.NormalProjectiveSurface
