import KltDP.Geometry.NormalModelFrameFromTargetLift
import KltDP.Geometry.TargetOpenCanonicalCoordinate

/-!
# A normalized actual local frame with the original detected canonical order

Proper birationality constructs the target isomorphism open and its original
inverse lift. Its fixed source-induced Cartier divisor has exactly the
original Weil pushforward. The proved normalization construction applies
to the given target reference, and the original common-open order theorem
identifies the resulting frame order with the original source coefficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalModelFrameNormalization

open NormalModelCanonical ProperBirationalCanonicalOpen

attribute [local instance] integralSchemeStalk_isDomain

local instance resultIntegralOpen {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (U : X.toScheme.Opens) [Nonempty U.toScheme] :
    IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- The actual detected model point has a canonical frame normalized to the
given original target reference, with precisely the original source coefficient. -/
theorem exists_normalized_frame
    {k : Type u} [Field k] [IsAlgClosed k] (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (v : V ⟶ X.toScheme) (iS : W ⟶ S.toScheme) (iV : W ⟶ V)
    [IsOpenImmersion iS] [IsOpenImmersion iV]
    (hcomm : iS ≫ π = iV ≫ v)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (w : W) (x : V) (hwV : iV.base w = x)
    [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (D : S.PrimeCurve) (hwS : iS.base w = D.genericPoint)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (U : X.toScheme.Opens) [Nonempty U.toScheme]
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (KU : CartierDivisor U.toScheme)
    (eKU : cartierDivisorModule U.toScheme KU ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (U.ι ≫ X.structureMorphism) 2)
    (hpush : BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom KS) =
      OpenCartierWeil.restrictedWeilHom U KU) :
    ∃ F : LocalFrame (v ≫ X.structureMorphism) x,
      IsNormalized X U KU eKU v x F ∧ F.order = S.cartierToWeilHom KS D := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let B := targetIsomorphismOpen π
  letI : IsIntegral B.toScheme := ProperBirationalCanonicalOpen.isIntegral π hbir
  letI : Nonempty B.toScheme := inferInstance
  letI : IsOpenImmersion (lift π) := lift_isOpenImmersion π
  letI : GenericPointPreserving (lift π) :=
    ⟨genericPoint_eq_of_isOpenImmersion (lift π)⟩
  have hB : ∀ C : X.PrimeCurve, C.genericPoint ∈ B :=
    TargetOpenCartierPushforward.prime_genericPoint_mem π hbir
  have hext : OpenCartierWeil.restrictedWeilHom B
      (DominantCartierPullback.pullbackHom (lift π) KS) =
      OpenCartierWeil.restrictedWeilHom U KU :=
    (TargetOpenCartierPushforward.restrictedWeilHom_eq_pushforward π hbir KS).trans hpush
  obtain ⟨F, hF, horder⟩ := exists_normalized_frame_of_target_lift
    S X π v iS iV hcomm hπ w x hwV KS eKS B U (lift π) (lift_comp π)
      hB hU KU eKU hext
  refine ⟨F, hF, horder.trans ?_⟩
  exact CommonOpenCanonicalLocalFrame.localFrame_order
    S X π v iS iV hcomm hπ w x hwV KS eKS D hwS

end KltDP.Geometry.NormalModelFrameNormalization

#check @KltDP.Geometry.NormalModelFrameNormalization.exists_normalized_frame
#print axioms KltDP.Geometry.NormalModelFrameNormalization.exists_normalized_frame
