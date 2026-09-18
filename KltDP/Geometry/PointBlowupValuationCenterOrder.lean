import KltDP.Geometry.PointBlowupValuationCofinality
import KltDP.Geometry.BirationalOpenSpanOrder
import KltDP.Geometry.PrimeCurveOrder
import KltDP.Geometry.SmoothSurfaceRelativeDimension

/-!
# The original valuation centre and order on one smooth resolution

The original model may be nonproper. Completion and the common-open order
comparison produce a prime on a point-blowup resolution of the original X
with exactly the original centre on X and order on every unit of K(X). The comparison uses
the actual function-field map of the resulting resolution.

This is divisorial order detection, not canonical-form or discrepancy
compatibility. The original DVR point is an ordinary geometric input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

attribute [local instance] integralSchemeStalk_isDomain

/-- A divisorial point on any integral finite-type birational model is
realized on an actual smooth resolution with its original K(X)-order. -/
theorem exists_pointBlowup_resolution_detecting_center_order
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    {V : Scheme.{u}} [IsIntegral V]
    (t : T.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    [LocallyOfFiniteType (v ≫ X.structureMorphism)]
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (htk : t ≫ X.structureMorphism = T.structureMorphism)
    (x : CodimensionOnePoint V) [IsDiscreteValuationRing (V.presheaf.stalk x.val)] :
    letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme)
        (hπ : IsResolution S X π) (D : S.PrimeCurve),
      letI : GenericPointPreserving π := ⟨hπ.birational.map_genericPoint⟩
      IsSmoothOfRelativeDimension 2 S.structureMorphism ∧
      (∃ b : S.toScheme ⟶ T.toScheme,
        IsResolution S T b ∧ IsPointBlowupSequence S T b ∧ π = b ≫ t) ∧
      π.base D.genericPoint = v.base x.val ∧
      ∀ a : X.toScheme.functionFieldˣ,
        D.order (Units.map (functionFieldMap π).hom.toMonoidHom a) =
          stalkDivisorOrder V x.val (Units.map (functionFieldMap v).hom.toMonoidHom a) := by
  letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
  obtain ⟨U, hU, hx, Z, j, p, hZ, h⟩ :=
    exists_pointBlowup_detection_of_valuation_point T X t v ht hv htk x
  letI := hZ
  obtain ⟨S, b, q, D, hj, hproperp, hbirp, hjp, hbR, hsmooth, hseq,
    hbirq, hproperq, hqk, hfac, hD, hstalk, himage⟩ := h
  letI : IsOpenImmersion j := hj
  letI : Nonempty U.toScheme := ⟨⟨x.val, hx⟩⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  letI : GenericPointPreserving p := ⟨hbirp.map_genericPoint⟩
  letI : GenericPointPreserving q := ⟨hbirq.map_genericPoint⟩
  let π := q ≫ p
  have hbirπ : IsBirationalScheme π :=
    (BirationalComposition.isBirationalScheme_comp_iff q p).mpr ⟨hbirq, hbirp⟩
  have hπ : IsResolution S X π :=
    ⟨by simpa only [π, Category.assoc] using hqk,
      hbR.regular, ⟨hbirπ.map_genericPoint, hbirπ.isIso_stalkMap_genericPoint⟩⟩
  letI : IsIso (q.stalkMap D.genericPoint) := hstalk
  letI : IsDiscreteValuationRing (S.stalk D.genericPoint) :=
    D.genericPoint_isDiscreteValuationRing
  letI : IsSmooth S.structureMorphism := hsmooth
  have hcenter : π.base D.genericPoint = v.base x.val := by
    change p.base (q.base D.genericPoint) = v.base x.val
    rw [hD]
    exact congrArg (fun f : U.toScheme ⟶ X.toScheme => f.base ⟨x.val, hx⟩) hjp
  refine ⟨S, π, hπ, D, S.isSmoothOfRelativeDimension_two,
    ⟨b, hbR, hseq, hfac⟩, hcenter, ?_⟩
  intro a
  rw [D.order_eq_stalkDivisorOrder]
  letI : IsDiscreteValuationRing (V.presheaf.stalk (U.ι.base ⟨x.val, hx⟩)) := by
    change IsDiscreteValuationRing (V.presheaf.stalk x.val)
    infer_instance
  exact BirationalOpenSpanOrder.order_eq_through_original_open
    U.ι j v p q hjp.symm D.genericPoint ⟨x.val, hx⟩ hD a

end KltDP.Geometry

#check @KltDP.Geometry.exists_pointBlowup_resolution_detecting_center_order
#print axioms KltDP.Geometry.exists_pointBlowup_resolution_detecting_center_order
