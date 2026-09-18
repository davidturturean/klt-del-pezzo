import KltDP.Geometry.ContractionCanonicalSquare
import KltDP.Geometry.ContractionNumericalRank

/-!
# The original canonical-square plus Picard-rank sum is unchanged

Both terms are the original geometric invariants. The exact rank increment
and canonical-square decrement are derived from the same actual contraction.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsContraction

open SmoothCanonicalExteriorComparison

/-- The original Noether sum is preserved by contraction of the actual
minus-one curve, for any actual canonical Cartier representatives. -/
theorem canonical_square_add_picardRank_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
    {E : S.PrimeCurve} (hb : IsContraction S T b E)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hminus : IsMinusOneCurve hS E)
    (KS : CartierDivisor S.toScheme) (KT : CartierDivisor T.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅ relativeDifferentialExterior S.structureMorphism 2)
    (eKT : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2) :
    S.intersectionPairing hS KS KS + (S.picardRank : ℤ) =
      T.intersectionPairing hb.regular KT KT + (T.picardRank : ℤ) := by
  rw [hb.canonical_square_eq_sub_one hS hminus KS KT eKS eKT,
    hb.picardRank_eq_add_one hS hminus, Nat.cast_add, Nat.cast_one]
  ring

end KltDP.Geometry.IsContraction

#check @KltDP.Geometry.IsContraction.canonical_square_add_picardRank_eq
#print axioms KltDP.Geometry.IsContraction.canonical_square_add_picardRank_eq
