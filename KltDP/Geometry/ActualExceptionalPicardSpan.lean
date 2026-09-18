import KltDP.Geometry.ActualExceptionalNegativeDefinite
import KltDP.Geometry.RationalNullCurveSpan
import KltDP.Geometry.ExceptionalNegativeDefinite

/-!
# Negativity on the original exceptional rational Picard span

The positive-square orthogonal divisor is constructed from projectivity of
the actual target and the original proper birational morphism. Independence
in the original numerical quotient implies independence of the original
rational Picard classes; the quotient is injective on their span. This
discharges the two formerly supplied exceptional-pairing conditions for
the original rational Picard intersection form.

The existing selected Hodge argument remains an explicitly isolated
literature dependency. No resolution existence, exceptional rationality,
Picard rank formula, or count of singular points is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Support.NegativeDefinite

universe u

namespace KltDP.Geometry.ActualExceptionalPicardSpan

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- The existing exceptional-class set is the range of the original rational
Picard classes indexed by the actual contracted primes. -/
theorem exceptionalClasses_eq_range :
    NormalProjectiveSurface.exceptionalClasses π hregular =
      Set.range (fun C : {C : S.PrimeCurve // IsExceptionalCurve π C} =>
        S.primeCurveRationalPicardClass hregular C.val) := by
  ext v
  constructor
  · rintro ⟨C, hC, rfl⟩
    exact ⟨⟨C, hC⟩, rfl⟩
  · rintro ⟨C, rfl⟩
    exact ⟨C.val, C.property, rfl⟩

variable [IsProper π] (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π)

include hπ hbir in
/-- The original rational Picard classes of all actual contracted primes
are linearly independent, without an input independence assertion. -/
theorem linearIndependent : LinearIndependent ℚ
    (fun C : {C : S.PrimeCurve // IsExceptionalCurve π C} =>
      S.primeCurveRationalPicardClass hregular C.val) := by
  obtain ⟨H, hH, hnull⟩ :=
    ActualExceptionalNegativeDefinite.exists_positive_square_orthogonal_divisor
      π hπ hbir hregular
  exact RationalNullCurveSpan.linearIndependent S hregular H hH
    Subtype.val Subtype.val_injective (fun C => hnull C.val C.property)

include hπ hbir in
/-- Every nonzero class in the original exceptional rational Picard span
has strictly negative square in the original rational Picard pairing. -/
theorem square_neg_on_span (c : S.RationalPicard)
    (hc : c ∈ Submodule.span ℚ
      (NormalProjectiveSurface.exceptionalClasses π hregular)) (hne : c ≠ 0) :
    S.rationalPicardIntersectionBilinForm hregular c c < 0 := by
  obtain ⟨H, hH, hnull⟩ :=
    ActualExceptionalNegativeDefinite.exists_positive_square_orthogonal_divisor
      π hπ hbir hregular
  rw [exceptionalClasses_eq_range] at hc
  exact RationalNullCurveSpan.square_neg_on_span S hregular H hH
    Subtype.val Subtype.val_injective (fun C => hnull C.val C.property) c hc hne

include hπ hbir in
/-- The old exceptional semidefiniteness input is now produced for the
actual morphism and the original rational Picard intersection form. -/
theorem exceptionalPairingNegSemidefinite :
    NormalProjectiveSurface.ExceptionalPairingNegSemidefinite π hregular
      (S.rationalPicardIntersectionBilinForm hregular) := by
  obtain ⟨H, hH, hnull⟩ :=
    ActualExceptionalNegativeDefinite.exists_positive_square_orthogonal_divisor
      π hπ hbir hregular
  change NegSemidefiniteOn (S.rationalPicardIntersectionBilinForm hregular)
    (NormalProjectiveSurface.exceptionalClasses π hregular)
  rw [exceptionalClasses_eq_range]
  exact RationalNullCurveSpan.negSemidefiniteOn S hregular H hH
    Subtype.val Subtype.val_injective (fun C => hnull C.val C.property)

include hπ hbir in
/-- The old exceptional nondegeneracy input is now produced on that same
original rational Picard span. -/
theorem exceptionalPairingNondegenerate :
    NormalProjectiveSurface.ExceptionalPairingNondegenerate π hregular
      (S.rationalPicardIntersectionBilinForm hregular) := by
  obtain ⟨H, hH, hnull⟩ :=
    ActualExceptionalNegativeDefinite.exists_positive_square_orthogonal_divisor
      π hπ hbir hregular
  change NondegenerateOn (S.rationalPicardIntersectionBilinForm hregular)
    (NormalProjectiveSurface.exceptionalClasses π hregular)
  rw [exceptionalClasses_eq_range]
  exact RationalNullCurveSpan.nondegenerateOn S hregular H hH
    Subtype.val Subtype.val_injective (fun C => hnull C.val C.property)

end KltDP.Geometry.ActualExceptionalPicardSpan

#print axioms KltDP.Geometry.ActualExceptionalPicardSpan.linearIndependent
#print axioms KltDP.Geometry.ActualExceptionalPicardSpan.exceptionalPairingNegSemidefinite
#print axioms KltDP.Geometry.ActualExceptionalPicardSpan.exceptionalPairingNondegenerate
