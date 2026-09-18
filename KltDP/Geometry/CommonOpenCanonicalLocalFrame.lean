import KltDP.Geometry.NormalModelLocalFrameConstructor
import KltDP.Geometry.CanonicalExteriorCommonOpenComparison

/-!
# The original smooth common open supplies a canonical local frame

The detected common open of an arbitrary original model and a smooth
surface directly supplies a smooth neighborhood through the original model
point. The actual source canonical Cartier divisor and differential map
give its local frame. Its original model order is the source prime-curve
coefficient, without assuming a comparison of canonical coefficients.

Normalization to an independently chosen target reference is a separate
step; this constructor does not assert it.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CommonOpenCanonicalLocalFrame

open OpenImmersionRational DominantCartierPullback

attribute [local instance] integralSchemeStalk_isDomain

local instance frameOpenGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (e : Y ⟶ Z) [IsOpenImmersion e] : GenericPointPreserving e :=
  ⟨genericPoint_eq_of_isOpenImmersion e⟩

variable {k : Type u} [Field k] (S X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (π : S.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    (iS : W ⟶ S.toScheme) (iV : W ⟶ V)
    [IsOpenImmersion iS] [IsOpenImmersion iV]
    (hcomm : iS ≫ π = iV ≫ v)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (w : W) (x : V) (hwV : iV.base w = x)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)

/-- The literal common-open maps construct the original local frame. -/
def localFrame : NormalModelCanonical.LocalFrame (v ≫ X.structureMorphism) x := by
  have hσ := CanonicalExteriorCommonOpen.structure_eq X.structureMorphism π v
    S.structureMorphism (v ≫ X.structureMorphism) hπ rfl iS iV hcomm
  letI : IsSmoothOfRelativeDimension 2 (iV ≫ (v ≫ X.structureMorphism)) :=
    hσ ▸ IsLocalAtSource.comp (P := @IsSmoothOfRelativeDimension 2)
      (inferInstance : IsSmoothOfRelativeDimension 2 S.structureMorphism) iS
  exact NormalModelCanonical.LocalFrame.ofCanonicalDivisor
    (v ≫ X.structureMorphism) iV w x hwV (pullbackHom iS KS)
    (CartierRationalCoordinate.canonicalOpenPullbackIso iS S.structureMorphism
      (iV ≫ (v ≫ X.structureMorphism)) hσ KS eKS)

/-- The constructed local frame retains the original source Cartier coefficient. -/
theorem localFrame_order [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (D : S.PrimeCurve) (hwS : iS.base w = D.genericPoint) :
    (localFrame S X π v iS iV hcomm hπ w x hwV KS eKS).order =
      S.cartierToWeilHom KS D := by
  letI : IsDiscreteValuationRing (W.presheaf.stalk w) :=
    stalk_isDiscreteValuationRing_of_isOpenImmersion iV w x hwV
  letI := D.genericPoint_isDiscreteValuationRing
  have h := NormalModelCanonical.LocalFrame.order_eq_cartierOrderAt
    (localFrame S X π v iS iV hcomm hπ w x hwV KS eKS)
  change (localFrame S X π v iS iV hcomm hπ w x hwV KS eKS).order =
    cartierOrderAt W (pullbackHom iS KS) w at h
  apply h.trans
  rw [pullbackHom_eq_cartierRestrictionHom]
  exact cartierOrderAt_cartierRestrictionHom iS KS w D.genericPoint hwS

end KltDP.Geometry.CommonOpenCanonicalLocalFrame

#check @KltDP.Geometry.CommonOpenCanonicalLocalFrame.localFrame
#print axioms KltDP.Geometry.CommonOpenCanonicalLocalFrame.localFrame_order
