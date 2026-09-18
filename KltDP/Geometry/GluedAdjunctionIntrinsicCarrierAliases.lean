import KltDP.Geometry.GluedAdjunctionIntrinsicOriginalHom

/-! Definitional chart projections, without unfolding the whole gluing construction. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicCarrierAliases

/-- The original chart object is its original affine quotient scheme. -/
theorem chart_scheme {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    I.glueData.toGlueData.U U = I.glueDataObj U := rfl

/-- The canonical quotient commutative-semiring dictionary is unchanged. -/
theorem quotient_commSemiring (B : Type u) [CommRing B] (J : Ideal B) :
    (Ideal.Quotient.commRing J).toCommSemiring = Ideal.Quotient.commSemiring J := rfl

end KltDP.Geometry.GluedAdjunctionIntrinsicCarrierAliases
