import KltDP.Geometry.PointBlowupValuationCofinality
import KltDP.Geometry.ProperBirationalCommonOpenAtValuation
import KltDP.Geometry.NormalFiniteTypeValuationPoint
import KltDP.Geometry.SmoothSurfaceRelativeDimension

/-!
# The detected divisor and original normal model share an actual open

For an arbitrary normal finite-type birational model, the original
divisorial point lies on an actual common open with a smooth point-blowup
resolution. Both original point images and the triangle over the original
base are retained. This strengthens order detection with the local maps
needed to compare the original differential sheaves and canonical forms.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry
attribute [local instance] integralSchemeStalk_isDomain

theorem exists_smooth_resolution_common_open_at_normal_model_divisor
    {k : Type u} [Field k] [IsAlgClosed k]
    (T X : NormalProjectiveSurface k) [IsSmooth T.structureMorphism]
    {V : Scheme.{u}} [IsIntegral V] (hnormal : IsNormalScheme V)
    (t : T.toScheme ⟶ X.toScheme) (v : V ⟶ X.toScheme)
    [LocallyOfFiniteType (v ≫ X.structureMorphism)]
    (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)
    (htk : t ≫ X.structureMorphism = T.structureMorphism)
    (x : CodimensionOnePoint V) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsResolution S X π ∧ IsSmoothOfRelativeDimension 2 S.structureMorphism ∧
      (∃ b : S.toScheme ⟶ T.toScheme,
        IsResolution S T b ∧ IsPointBlowupSequence S T b ∧ π = b ≫ t) ∧
      ∃ (D : S.PrimeCurve) (W : Scheme.{u}) (iS : W ⟶ S.toScheme) (iV : W ⟶ V) (w : W),
        IsOpenImmersion iS ∧ IsOpenImmersion iV ∧
        iS.base w = D.genericPoint ∧ iV.base w = x.val ∧ iS ≫ π = iV ≫ v := by
  letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
  letI : IsDiscreteValuationRing (V.presheaf.stalk x.val) :=
    normalFiniteTypePoint_isDiscreteValuationRing (v ≫ X.structureMorphism) hnormal x
  obtain ⟨U, hU, hx, Z, j, p, hZ, h⟩ :=
    exists_pointBlowup_detection_of_valuation_point T X t v ht hv htk x
  letI := hZ
  obtain ⟨S, b, q, D, hj, hproperp, hbirp, hjp, hbR, hsmooth, hseq,
    hbirq, hproperq, hqk, hfac, hD, hstalk, himage⟩ := h
  letI : IsOpenImmersion j := hj
  letI : IsProper q := hproperq
  letI : GenericPointPreserving q := ⟨hbirq.map_genericPoint⟩
  letI : GenericPointPreserving p := ⟨hbirp.map_genericPoint⟩
  letI : Nonempty U.toScheme := ⟨⟨x.val, hx⟩⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let y : U.toScheme := ⟨x.val, hx⟩
  letI : ValuationRing (V.presheaf.stalk (U.ι.base y)) := by
    change ValuationRing (V.presheaf.stalk x.val)
    infer_instance
  letI : ValuationRing (U.toScheme.presheaf.stalk y) :=
    (OpenImmersionValuationPoint.stalk_valuationRing_iff U.ι y).mp inferInstance
  letI : ValuationRing (Z.presheaf.stalk (j.base y)) :=
    (OpenImmersionValuationPoint.stalk_valuationRing_iff j y).mpr inferInstance
  obtain ⟨W, iS, iU, w, hiS, hiU, hwS, hwU, hcomm⟩ :=
    exists_common_open_at_valuation_point q hbirq j D.genericPoint y hD
  letI : IsOpenImmersion iS := hiS
  letI : IsOpenImmersion iU := hiU
  letI : IsSmooth S.structureMorphism := hsmooth
  let π := q ≫ p
  have hbirπ : IsBirationalScheme π :=
    (BirationalComposition.isBirationalScheme_comp_iff q p).mpr ⟨hbirq, hbirp⟩
  have hπ : IsResolution S X π :=
    ⟨by simpa only [π, Category.assoc] using hqk,
      hbR.regular, ⟨hbirπ.map_genericPoint, hbirπ.isIso_stalkMap_genericPoint⟩⟩
  have hover : iS ≫ π = (iU ≫ U.ι) ≫ v := by
    change iS ≫ q ≫ p = (iU ≫ U.ι) ≫ v
    rw [← Category.assoc, hcomm, Category.assoc, hjp, ← Category.assoc]
  refine ⟨S, π, hπ, S.isSmoothOfRelativeDimension_two,
    ⟨b, hbR, hseq, hfac⟩, D, W, iS, iU ≫ U.ι, w, hiS, inferInstance,
    hwS, ?_, hover⟩
  change U.ι.base (iU.base w) = x.val
  rw [hwU]
  rfl

end KltDP.Geometry

#check @KltDP.Geometry.exists_smooth_resolution_common_open_at_normal_model_divisor
#print axioms KltDP.Geometry.exists_smooth_resolution_common_open_at_normal_model_divisor
