import KltDP.Geometry.WeilClassRationalRelation
import KltDP.Geometry.AmpleCartierFromWeilClass
import KltDP.Geometry.QAmpleIntegralMultiple

/-!
# Zero and negative signs in an actual integral canonical-class relation

A nonzero integral multiple of the original Weil class being zero means
rational linear triviality in the existing principal-divisor quotient.
For a negative ample coefficient, negate the original relation and apply
the proved ample Cartier representative theorem to the negative divisor.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Torsion of the actual integral Weil class implies rational linear
triviality of the actual divisor, rather than merely numerical triviality. -/
theorem qLinearlyEquivalent_zero_of_nonzero_zsmul_class_eq_zero
    (D : X.WeilDivisor) (c : ℤ) (hc : c ≠ 0)
    (h : c • X.weilClassMap D = 0) :
    X.QLinearlyEquivalent (rationalizeWeilDivisor X D) 0 := by
  have hrel : c • X.weilClassMap D + (0 : ℤ) • (0 : X.WeilClassGroup) = 0 := by
    simpa only [zero_zsmul, add_zero] using h
  have hr := X.rationalization_formula_of_integral_relation
    c 0 (X.weilClassMap D) 0 hc hrel
  have hz : X.weilClassRationalization (X.weilClassMap D) = 0 := by
    simpa only [Int.cast_zero, neg_zero, zero_div, zero_smul] using hr
  apply (X.rationalWeilClassMap_eq_iff (rationalizeWeilDivisor X D) 0).mp
  simpa only [weilClassRationalization_class, map_zero] using hz

/-- A negative ample coefficient in the original canonical relation
produces an actual ample Cartier numerator of the positive divisor. -/
theorem qAmple_of_negative_canonical_relation
    (D : X.WeilDivisor) (L : InvertibleSheaf X.toScheme)
    (c d : ℤ) (hc : 0 < c) (hd : d < 0) (hL : AmpleSerre.IsAmple L)
    (h : c • X.weilClassMap D +
      d • X.picardToWeilClassHom (Additive.ofMul L.toPic) = 0) :
    X.QAmple (rationalizeWeilDivisor X D) := by
  have hneg : c • X.weilClassMap (-D) +
      (-d) • X.picardToWeilClassHom (Additive.ofMul L.toPic) = 0 := by
    simpa only [map_neg, zsmul_neg, neg_smul, neg_add, neg_zero] using
      congrArg (fun z : X.WeilClassGroup => -z) h
  obtain ⟨N, hN, B, hB, hBample⟩ :=
    X.exists_ample_anticanonical_multiple_of_positive_relation
      (-D) L c (-d) hc (neg_pos.mpr hd) hL hneg
  apply X.qAmple_of_ample_integral_multiple D N hN B _ hBample
  simpa only [neg_neg] using hB

end KltDP.Geometry.NormalProjectiveSurface
