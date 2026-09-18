import KltDP.Geometry.PointBlowupValuationOrderDetection
import KltDP.Geometry.NormalFiniteTypeValuationPoint
import KltDP.Geometry.SmoothSurfaceRelativeDimension

/-!
# Smooth resolutions detect original divisors on normal finite-type models

Normality and finite type derive the original divisorial DVR. The proved
order-detection theorem supplies an actual smooth point-blowup resolution;
its original structure morphism has smooth relative dimension two.
The model need not be proper or projective. Canonical-form compatibility
and discrepancy inequalities are separate from this order statement.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

attribute [local instance] integralSchemeStalk_isDomain

/-- Every divisor on an original normal finite-type birational model
has exactly its original K(X)-order on a smooth projective resolution. -/
theorem exists_smooth_resolution_detecting_normal_model_order
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
      ∀ a : X.toScheme.functionFieldˣ,
        D.order (Units.map (functionFieldMap π).hom.toMonoidHom a) =
          stalkDivisorOrder V x.val (Units.map (functionFieldMap v).hom.toMonoidHom a) := by
  letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
  letI : IsDiscreteValuationRing (V.presheaf.stalk x.val) :=
    normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
  obtain ⟨S, π, hπ, D, hsmooth, hseq, horder⟩ :=
    exists_pointBlowup_resolution_detecting_order T X t v ht hv htk x
  letI : IsSmooth S.structureMorphism := hsmooth
  exact ⟨S, π, hπ, D, S.isSmoothOfRelativeDimension_two, hseq, horder⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_smooth_resolution_detecting_normal_model_order
#print axioms KltDP.Geometry.exists_smooth_resolution_detecting_normal_model_order
