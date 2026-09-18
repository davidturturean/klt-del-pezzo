import KltDP.Geometry.GluedAdjunctionSectionAgreement
import KltDP.Geometry.GluedAdjunctionBasisExtension
import KltDP.Geometry.GluedAdjunctionBasisMapOpenLaws
import KltDP.Geometry.GluedAdjunctionBasisRestrictionLaws
import KltDP.Geometry.GluedAdjunctionNativeApplication
import KltDP.Geometry.GluedAdjunctionNativeApplicationTerm

/-!
# Adjunction for the original smooth curve and its original normal sheaf

Original smoothness and regular local equations give the proved basis of
simultaneous charts. Their original adjunction maps agree by the proved
principal refinement squares and sheaf separation. The existing basis
extension glues these actual linear maps, and their actual bijective
components make the resulting original global module map an isomorphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.GluedSmoothCurveAdjunction

open GluedAdjunctionChartBasis

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I)

/-- The actual original adjunction components form a natural transformation on the proved basis. -/
def basisMap :
    (inducedFunctor (Chart.sourceOpen (f := f) (I := I))).op ⋙
        (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)).val.presheaf ⟶
      (inducedFunctor (Chart.sourceOpen (f := f) (I := I))).op ⋙
        (GluedAdjunctionIntrinsicChart.targetSheaf f I).val.presheaf where
  app c := AddCommGrp.ofHom
    (GluedAdjunctionBasisSectionComponents.hom f I hI c.unop c.unop.sourceOpen le_rfl)
  naturality {c e} i := by
    let h : e.unop.sourceOpen ≤ c.unop.sourceOpen :=
      (show e.unop.sourceOpen ⟶ c.unop.sourceOpen from i.unop).le
    have hi : (homOfLE h).op = i := by
      congr 1
    have hAgree := GluedAdjunctionSectionAgreement.hom_eq f I hI e.unop c.unop
      e.unop.sourceOpen le_rfl h
    have hRes := GluedAdjunctionBasisSectionComponents.hom_res f I hI c.unop
      c.unop.sourceOpen e.unop.sourceOpen h le_rfl
    have hPartial := GluedAdjunctionBasisRestrictionLaws.naturality
      (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f))
      (GluedAdjunctionIntrinsicChart.targetSheaf f I)
      (Chart.sourceOpen (f := f) (I := I)) i h hi
      (GluedAdjunctionBasisSectionComponents.hom f I hI c.unop c.unop.sourceOpen le_rfl)
      (fun hV => GluedAdjunctionBasisSectionComponents.hom f I hI c.unop e.unop.sourceOpen hV)
      (GluedAdjunctionBasisSectionComponents.hom f I hI e.unop e.unop.sourceOpen le_rfl)
      hAgree
    exact_native_adjunction_application hPartial hRes

/-- Original scalar-linearity of every actual basis component. -/
theorem basisMap_smul (c : Chart f I) (r : Γ(I.glueData.glued, c.sourceOpen))
    (m : (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)).val.obj (op c.sourceOpen)) :
    (basisMap f I hI).app (op c) (r • m) =
      r • (show (GluedAdjunctionIntrinsicChart.targetSheaf f I).val.obj (op c.sourceOpen) from
        (basisMap f I hI).app (op c) m) :=
  GluedAdjunctionBasisMapOpenLaws.app_smul
    (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f))
    (GluedAdjunctionIntrinsicChart.targetSheaf f I)
    (Chart.sourceOpen (f := f) (I := I)) (basisMap f I hI) c
    (GluedAdjunctionBasisSectionComponents.hom f I hI c c.sourceOpen le_rfl) rfl
    (GluedAdjunctionBasisSectionComponents.hom_smul f I hI c c.sourceOpen le_rfl) r m

variable [IsSmoothOfRelativeDimension 2 f] [IsSmoothOfRelativeDimension 1 (I.gluedTo ≫ f)]

/-- The original local adjunction maps glued by the pinned basis extension. -/
def hom : SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f) ⟶
    GluedAdjunctionIntrinsicChart.targetSheaf f I := by
  let extension := GluedAdjunctionBasisExtension.hom (Chart.sourceOpen (f := f) (I := I))
    (GluedAdjunctionChartBasis.isBasis f I hI) (basisMap f I hI)
  have hLinear := basisMap_smul f I hI
  exact_native_adjunction_application extension hLinear

/-- The glued original map retains every original chart component. -/
theorem hom_app (c : Chart f I)
    (m : (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)).val.obj (op c.sourceOpen)) :
    (hom f I hI).val.app (op c.sourceOpen) m =
      GluedAdjunctionBasisSectionComponents.hom f I hI c c.sourceOpen le_rfl m := by
  let comparison := GluedAdjunctionBasisExtension.hom_app
    (Chart.sourceOpen (f := f) (I := I))
    (GluedAdjunctionChartBasis.isBasis f I hI) (basisMap f I hI)
  have hLinear := basisMap_smul f I hI
  have onBasis := native_adjunction_application% comparison hLinear
  have atChart := native_adjunction_application% onBasis c
  exact_native_adjunction_application atChart m

/-- The original glued map is invertible because its actual basis components are bijective. -/
theorem hom_isIso : IsIso (hom f I hI) := by
  let invertible := GluedAdjunctionBasisExtension.hom_isIso
    (Chart.sourceOpen (f := f) (I := I)) (GluedAdjunctionChartBasis.isBasis f I hI)
    (basisMap f I hI)
  have hLinear := basisMap_smul f I hI
  have fromComponents := native_adjunction_application% invertible hLinear
  have hBij := fun c : Chart f I =>
    GluedAdjunctionBasisSectionComponents.hom_bijective f I hI c c.sourceOpen le_rfl
  exact_native_adjunction_application fromComponents hBij

/-- The original differential sheaf of the smooth curve is the original ambient
top differential sheaf restricted to it and tensored with its original normal sheaf. -/
def iso : SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f) ≅
    GluedAdjunctionIntrinsicChart.targetSheaf f I := by
  letI := hom_isIso f I hI
  exact asIso (hom f I hI)

end KltDP.Geometry.GluedSmoothCurveAdjunction
