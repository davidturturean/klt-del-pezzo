import KltDP.Geometry.ContractionPicardPairing
import KltDP.LinearAlgebra.OrthogonalIntegerDual
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Unimodularity through the actual minus-one contraction

The normalized original Picard splitting carries the actual integral pairing
to the target pairing orthogonally summed with [-1]. The original additive
integral-dual test is therefore equivalent on the source and target.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The original unimodularity predicate is exactly the actual bilinear
form's map to the additive integral dual. -/
theorem NormalProjectiveSurface.picardUnimodular_iff_bilinForm
    (X : NormalProjectiveSurface k)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x) :
    X.PicardUnimodular hX ↔ Function.Bijective
      (fun p => (X.integralPicardIntersectionBilinForm hX p).toAddMonoidHom) := by
  unfold NormalProjectiveSurface.PicardUnimodular
  apply Iff.of_eq
  congr 1
  funext p
  apply AddMonoidHom.ext
  intro q
  exact (X.integralPicardIntersectionBilinForm_apply hX p q).symm

namespace IsContraction

variable {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {E : S.PrimeCurve} (hb : IsContraction S T b E)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (hminus : IsMinusOneCurve hS E)

/-- The same original normalized splitting in additive notation. -/
def picardDecompositionAdd : Additive S.toScheme.Pic ≃+ (Additive T.toScheme.Pic × ℤ) :=
  (hb.picardDecomposition hS hminus).toAdditive.trans
    ((AddEquiv.prodAdditive T.toScheme.Pic (Multiplicative ℤ)).trans
      (AddEquiv.prodCongr (AddEquiv.refl _)
        (AddEquiv.additiveMultiplicative ℤ)))

include hminus in
/-- Unimodularity of the original integral Picard forms is preserved in both
directions by the actual contraction of the actual minus-one curve. -/
theorem picardUnimodular_iff : S.PicardUnimodular hS ↔ T.PicardUnimodular hb.regular := by
  rw [S.picardUnimodular_iff_bilinForm hS, T.picardUnimodular_iff_bilinForm hb.regular]
  apply KltDP.LinearAlgebra.dual_bijective_iff_of_orthogonal_int
    (T.integralPicardIntersectionBilinForm hb.regular)
    (S.integralPicardIntersectionBilinForm hS) (hb.picardDecompositionAdd hS hminus).symm
  intro x y
  rw [S.integralPicardIntersectionBilinForm_apply,
    T.integralPicardIntersectionBilinForm_apply]
  exact hb.picardDecomposition_pairing hS hminus x.1.toMul y.1.toMul x.2 y.2

end IsContraction
end KltDP.Geometry

#check @KltDP.Geometry.IsContraction.picardUnimodular_iff
#print axioms KltDP.Geometry.IsContraction.picardUnimodular_iff
