import KltDP.Geometry.GluedAdjunctionChartBasis
import KltDP.Geometry.GluedAdjunctionIntrinsicChartRefinement
import KltDP.Geometry.GluedAdjunctionNativeComponentNormalization

/-!
# Agreement of the original adjunction maps on common principal refinements

Each refined map is the pullback of the original intrinsic chart map,
conjugated by the original pullback-composition and equality comparisons.
The proved basic-open square identifies it with the original smaller
chart map. A common principal open and the proved equation independence
therefore identify the two original maps near every intersection point.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionCommonRefinement

open GluedAdjunctionChartBasis

private theorem normalize_square {C : Type*} [Category C] {S₀ T₀ S T : C}
    (eS : S₀ ≅ S) (eT : T₀ ≅ T) (a : S₀ ⟶ T₀) (b : S ⟶ T)
    (h : a ≫ eT.hom = eS.hom ≫ b) : eS.inv ≫ a ≫ eT.hom = b := by
  rw [h, Iso.inv_hom_id_assoc]

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I)

/-- The original intrinsic chart map with the chart's proved smoothness dictionaries. -/
def iso (c : Chart f I) :
    (schemeModulePullback (I.glueData.ι c.U)).obj
        (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)) ≅
      (schemeModulePullback (I.glueData.ι c.U)).obj
        (GluedAdjunctionIntrinsicChart.targetSheaf f I) := by
  letI : Algebra k Γ(X, c.U.1) := GluedChartKaehlerPullback.chartAlgebra f c.U
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, c.U.1) := c.ambient
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Γ(X, c.U.1) ⧸ I.ideal c.U) := c.curve
  exact GluedAdjunctionIntrinsicChart.iso f I hI c.U c.d c.equation c.regular

/-- On the same original ambient open, changing the regular equation preserves the map. -/
theorem hom_heq_of_U_eq (c e : Chart f I) (h : c.U = e.U) :
    HEq (iso f I hI c).hom (iso f I hI e).hom := by
  obtain ⟨U, d, hU, hd, hA, hQ⟩ := c
  obtain ⟨V, e, hV, he, hA', hQ'⟩ := e
  dsimp only at h
  subst V
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1) := hA
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Γ(X, U.1) ⧸ I.ideal U) := hQ
  apply heq_of_eq
  exact congrArg (fun z => z.hom)
    (GluedAdjunctionIntrinsicChart.iso_eq f I hI U d hU hd e hV he)

/-- The original composition and equality comparisons at one original global object. -/
def refinementIso (c : Chart f I) (r : Γ(X, c.U.1)) (M : I.glueData.glued.Modules) :
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).obj
        ((schemeModulePullback (I.glueData.ι c.U)).obj M) ≅
      (schemeModulePullback (I.glueData.ι (X.affineBasicOpen r))).obj M :=
  (schemeModulePullbackCompIso (I.glueDataObjMap (X.affineBasicOpen_le r))
    (I.glueData.ι c.U)).app M ≪≫
      eqToIso (congrArg (fun j => (schemeModulePullback j).obj M)
        (I.glueDataObjMap_ι (X.affineBasicOpen r) c.U (X.affineBasicOpen_le r)))

/-- Restrict the original map and retain both original global-object comparisons. -/
def refinedHom (c : Chart f I) (r : Γ(X, c.U.1)) :
    (schemeModulePullback (I.glueData.ι (X.affineBasicOpen r))).obj
        (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)) ⟶
      (schemeModulePullback (I.glueData.ι (X.affineBasicOpen r))).obj
        (GluedAdjunctionIntrinsicChart.targetSheaf f I) :=
  (refinementIso f I c r (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f))).inv ≫
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).map (iso f I hI c).hom ≫
      (refinementIso f I c r (GluedAdjunctionIntrinsicChart.targetSheaf f I)).hom

end KltDP.Geometry.GluedAdjunctionCommonRefinement
