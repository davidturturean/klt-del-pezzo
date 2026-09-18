import KltDP.Geometry.QAmpleIntegralMultiple
import KltDP.Geometry.CartierRepresentativeWithPicardClass
import KltDP.Geometry.AmplePositivity

/-!
# Q-ampleness under an actual principal Weil correction

For integral Weil divisors with the same original Weil class, correct the
actual ample Cartier numerator by the existing principal-divisor producer.
It preserves the original Picard class, hence ampleness of its line sheaf.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Equality of the actual integral Weil classes transports an ample
Cartier numerator, with its positive denominator unchanged. -/
theorem qAmple_integral_of_weilClass_eq
    (D E : X.WeilDivisor) (hclass : X.weilClassMap D = X.weilClassMap E)
    (hD : X.QAmple (rationalizeWeilDivisor X D)) :
    X.QAmple (rationalizeWeilDivisor X E) := by
  obtain ⟨N, hN, B, hB, hBample⟩ := hD
  have hBW : X.cartierToWeilHom B = N • D := by
    apply rationalizeWeilDivisor_injective
    simpa only [map_nsmul] using hB
  have hnew : X.weilClassMap (N • E) = X.weilClassMap (X.cartierToWeilHom B) := by
    rw [hBW, map_nsmul, map_nsmul, hclass]
  obtain ⟨B', hB', hPic⟩ := X.exists_cartier_representative_with_picardClass
    (N • E) B hnew
  have hlines : (cartierDivisorInvertibleSheaf X.toScheme B).toPic =
      (cartierDivisorInvertibleSheaf X.toScheme B').toPic := by
    change (cartierPicardHom X.toScheme B).toMul =
      (cartierPicardHom X.toScheme B').toMul
    exact congrArg Additive.toMul hPic.symm
  exact X.qAmple_of_ample_integral_multiple E N hN B' hB'
    (AmplePositivity.isAmple_of_toPic_eq hlines hBample)

/-- Q-ampleness of an integral Weil divisor depends only on its actual
Weil class, through explicit ample Cartier representatives. -/
theorem qAmple_integral_iff_of_weilClass_eq
    (D E : X.WeilDivisor) (hclass : X.weilClassMap D = X.weilClassMap E) :
    X.QAmple (rationalizeWeilDivisor X D) ↔
      X.QAmple (rationalizeWeilDivisor X E) :=
  ⟨X.qAmple_integral_of_weilClass_eq D E hclass,
    X.qAmple_integral_of_weilClass_eq E D hclass.symm⟩

/-- The same class invariance for the negative of an integral divisor. -/
theorem qAmple_neg_integral_iff_of_weilClass_eq
    (D E : X.WeilDivisor) (hclass : X.weilClassMap D = X.weilClassMap E) :
    X.QAmple (-rationalizeWeilDivisor X D) ↔
      X.QAmple (-rationalizeWeilDivisor X E) := by
  have hneg : X.weilClassMap (-D) = X.weilClassMap (-E) := by
    simpa only [map_neg] using congrArg (fun z : X.WeilClassGroup => -z) hclass
  simpa only [map_neg] using X.qAmple_integral_iff_of_weilClass_eq (-D) (-E) hneg

end KltDP.Geometry.NormalProjectiveSurface
