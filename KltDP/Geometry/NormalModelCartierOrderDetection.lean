import KltDP.Geometry.PointBlowupValuationCenterOrder
import KltDP.Geometry.NormalFiniteTypeValuationPoint
import KltDP.Geometry.CartierPullbackValuationEquality

/-!
# Smooth resolutions preserve Cartier orders on every normal finite-type model

The original model need not be proper. Normality derives its divisorial
DVR, and the actual centre-and-order detection theorem produces a smooth
point-blowup resolution. Every original signed Cartier divisor then has
the same pullback order at the detected prime, simultaneously.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry
attribute [local instance] integralSchemeStalk_isDomain

theorem exists_smooth_resolution_detecting_normal_model_cartier_orders
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    {V : Scheme.{u}} [IsIntegral V] (hnormal : IsNormalScheme V)
    (t : T.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    [LocallyOfFiniteType (v ≫ X.structureMorphism)]
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (htk : t ≫ X.structureMorphism = T.structureMorphism)
    (x : CodimensionOnePoint V) :
    letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
    letI : IsDiscreteValuationRing (V.presheaf.stalk x.val) :=
      normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme)
        (hπ : IsResolution S X π) (D : S.PrimeCurve),
      letI : GenericPointPreserving π := ⟨hπ.birational.map_genericPoint⟩
      IsSmoothOfRelativeDimension 2 S.structureMorphism ∧
      (∃ b : S.toScheme ⟶ T.toScheme,
        IsResolution S T b ∧ IsPointBlowupSequence S T b ∧ π = b ≫ t) ∧
      π.base D.genericPoint = v.base x.val ∧
      ∀ A : CartierDivisor X.toScheme,
        S.cartierToWeilHom (DominantCartierPullback.pullbackHom π A) D =
          cartierOrderAt V (DominantCartierPullback.pullbackHom v A) x.val := by
  letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
  letI : IsDiscreteValuationRing (V.presheaf.stalk x.val) :=
    normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
  obtain ⟨S, π, hπ, D, hsmooth, hseq, hcenter, horder⟩ :=
    exists_pointBlowup_resolution_detecting_center_order T X t v ht hv htk x
  letI : GenericPointPreserving π := ⟨hπ.birational.map_genericPoint⟩
  letI := D.genericPoint_isDiscreteValuationRing
  refine ⟨S, π, hπ, D, hsmooth, hseq, hcenter, ?_⟩
  intro A
  change cartierOrderAt S.toScheme _ D.genericPoint = cartierOrderAt V _ x.val
  apply cartierOrderAt_pullback_eq_of_valuation_eq π v D.genericPoint x.val hcenter
  intro a
  simpa only [D.order_eq_stalkDivisorOrder] using horder a

end KltDP.Geometry

#check @KltDP.Geometry.exists_smooth_resolution_detecting_normal_model_cartier_orders
#print axioms KltDP.Geometry.exists_smooth_resolution_detecting_normal_model_cartier_orders
