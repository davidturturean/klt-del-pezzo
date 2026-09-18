import KltDP.Geometry.QCartierBirationalPrimeCoefficient
import KltDP.Geometry.SurfacePrimeCurvePoints

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.QCartierPullback

/-- An isomorphism of the original generic stalks identifies a target
prime and preserves all original rational Cartier coefficients there. -/
theorem exists_prime_preserving_coefficients_of_stalkMap_isIso
    {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (C : S.PrimeCurve) [IsIso (π.stalkMap C.genericPoint)] :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    ∃ D : X.PrimeCurve, π.base C.genericPoint = D.genericPoint ∧
      ∀ (B : X.RationalWeilDivisor) (hB : X.QCartier B), pullback π B hB C = B D := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  have hdim : ringKrullDim (X.toScheme.presheaf.stalk (π.base C.genericPoint)) = 1 :=
    (ringKrullDim_eq_of_ringEquiv
      (asIso (π.stalkMap C.genericPoint)).commRingCatIsoToRingEquiv).trans
        C.ringKrullDim_stalk_genericPoint
  let x : CodimensionOnePoint X.toScheme := ⟨π.base C.genericPoint, hdim⟩
  let D := X.codimensionOnePointToPrimeCurve x
  have hD : π.base C.genericPoint = D.genericPoint :=
    (X.codimensionOnePointToPrimeCurve_genericPoint x).symm
  exact ⟨D, hD, fun B hB => coefficient_of_maps_to_prime π hbir B hB C D hD⟩

end KltDP.Geometry.QCartierPullback

#print axioms KltDP.Geometry.QCartierPullback.exists_prime_preserving_coefficients_of_stalkMap_isIso
