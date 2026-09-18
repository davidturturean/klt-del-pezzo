import KltDP.Geometry.PointBlowupValuationCenterOrder
import KltDP.Geometry.QCartierPullbackValuationEquality
import KltDP.Geometry.ProjectiveFiniteType

/-!
# One smooth point-blowup model preserves all original Q-Cartier coefficients

For any actual prime of an original normal projective birational model,
derive its DVR and finite type from the original surface. The common
centre-and-order detection produces one smooth projective resolution
which simultaneously preserves all rational Cartier pullback coefficients.
Canonical representatives and discrepancies remain separate comparisons.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

theorem exists_smooth_resolution_detecting_qCartier_coefficients
    {k : Type u} [Field k] [IsAlgClosed k]
    (T V X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    (t : T.toScheme ⟶ X.toScheme) (v : V.toScheme ⟶ X.toScheme)
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (htk : t ≫ X.structureMorphism = T.structureMorphism)
    (hvk : v ≫ X.structureMorphism = V.structureMorphism) (C : V.PrimeCurve) :
    letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme)
        (hπ : IsResolution S X π) (D : S.PrimeCurve),
      letI : GenericPointPreserving π := ⟨hπ.birational.map_genericPoint⟩
      IsSmoothOfRelativeDimension 2 S.structureMorphism ∧
      (∃ b : S.toScheme ⟶ T.toScheme,
        IsResolution S T b ∧ IsPointBlowupSequence S T b ∧ π = b ≫ t) ∧
      ∀ (B : X.RationalWeilDivisor) (hB : X.QCartier B),
        QCartierPullback.pullback π B hB D = QCartierPullback.pullback v B hB C := by
  letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
  letI : LocallyOfFiniteType (v ≫ X.structureMorphism) := by
    rw [hvk]
    infer_instance
  letI : IsDiscreteValuationRing
      (V.toScheme.presheaf.stalk (V.primeCurveToCodimensionOnePoint C).val) := by
    change IsDiscreteValuationRing (V.stalk C.genericPoint)
    exact C.genericPoint_isDiscreteValuationRing
  obtain ⟨S, π, hπ, D, hsmooth, hseq, hcenter, horder⟩ :=
    exists_pointBlowup_resolution_detecting_center_order T X t v ht hv htk
      (V.primeCurveToCodimensionOnePoint C)
  letI : GenericPointPreserving π := ⟨hπ.birational.map_genericPoint⟩
  refine ⟨S, π, hπ, D, hsmooth, hseq, ?_⟩
  intro B hB
  apply QCartierPullback.coefficient_eq_of_valuation_eq π v D C hcenter _ B hB
  intro a
  simpa only [C.order_eq_stalkDivisorOrder] using horder a

end KltDP.Geometry

#check @KltDP.Geometry.exists_smooth_resolution_detecting_qCartier_coefficients
#print axioms KltDP.Geometry.exists_smooth_resolution_detecting_qCartier_coefficients
