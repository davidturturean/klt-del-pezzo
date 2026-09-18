import KltDP.Geometry.GluedAdjunctionIntrinsicTargetSquareCarriers
import KltDP.Geometry.GluedAdjunctionIntrinsicLocalSquareCarriers

/-!
# The measured target module aliases in the original adjunction diagram

The generic equalities identify the two native presentations of the same
ring dictionaries and normal module. Only the named target factors and the
local componentRestriction are exposed; the original maps remain unchanged.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicTargetInputAliases

private theorem ring_semiring (B : Type u) (s : CommRing B) :
    @CommSemiring.toSemiring B (@CommRing.toCommSemiring B s) =
      @Ring.toSemiring B (@CommRing.toRing B s) := rfl

private theorem quotient_dictionary (B : Type u) (s : CommRing B) :
    @Ideal.instHasQuotient_1 B s = @Ideal.instHasQuotient B s.toRing := rfl

private theorem normal_module (B : Type u) [CommRing B] (J : Ideal B) :
    PrincipalConormalTildeDual.normalModule J =
      NormalTwistedAdjunctionTensorChart.normalModule B J := rfl

/-- The same target square with the measured exterior/normal/ambient aliases reduced. -/
def target_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    have h := GluedAdjunctionIntrinsicTargetSquareCarriers.target_square
      f I hI U r d hU hd hAmbient
    dsimp only [ModuleCat.exteriorPower, AffineKaehlerTildeDerivation.differentialModule,
      normal_module, GluedNormalTwistedAdjunctionChart.ambientSheaf,
      ring_semiring, quotient_dictionary] at h
    exact h

/-- Expose only the original local target transition, leaving its passed source arrow intact. -/
def local_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    have h := GluedAdjunctionIntrinsicLocalSquareCarriers.local_square
      f I U r d hU hd hAmbient hCurve
    conv at h =>
      lhs
      rhs
      unfold AffineModuleTildeTensorPullbackRestriction.componentRestriction
    exact h

end KltDP.Geometry.GluedAdjunctionIntrinsicTargetInputAliases
