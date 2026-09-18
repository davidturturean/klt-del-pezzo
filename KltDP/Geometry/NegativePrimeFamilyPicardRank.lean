import KltDP.Geometry.DisjointNegativeCurvesRank
import KltDP.Geometry.RationalHodgeIndexProved
import KltDP.Geometry.SurfaceNumericalFinitenessProved
import KltDP.LinearAlgebra.NegativeGramDimension

/-!
# An actual negative prime family leaves a positive Picard direction

The original regular projective surface supplies finite numerical
dimension and an actual positive Hodge class. The existing strict
negative-Gram dimension theorem then bounds the family by its original
Picard rank, without a finiteness or positive-vector premise.
-/

noncomputable section
open AlgebraicGeometry
universe u v

namespace KltDP.Geometry.NormalProjectiveSurface

open DisjointNegativeCurvesRank KltDP.LinearAlgebra.CanonicalCorrection

/-- A negative actual prime family has strictly fewer elements than the original Picard rank. -/
theorem primeFamily_card_lt_picardRank_of_negativeGram
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    {I : Type v} [Fintype I] (C : I → X.PrimeCurve)
    (hneg : (negativeGram (X.numericalIntersectionBilinForm hX)
      (fun i => curveClass X hX (C i))).PosDef) : Fintype.card I < X.picardRank := by
  letI : FiniteDimensional ℚ X.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite X hX
  obtain ⟨a, ha, _⟩ := RationalHodgeIndexProved.signature X hX
  exact KltDP.LinearAlgebra.negativeGram_posDef_card_lt_finrank
    (X.numericalIntersectionBilinForm hX) (fun i => curveClass X hX (C i)) hneg ⟨a, ha⟩

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.primeFamily_card_lt_picardRank_of_negativeGram
