/-
Original pinned-API adapter following the finite affine-section argument in
Vilin97/MazurTheorem at 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SchemeModuleQuasicoherent.lean:685-763. Released under Apache 2.0.
-/
import KltDP.Geometry.AffineQuasicoherentFiniteGenerators
import KltDP.Geometry.AffineOpenModuleDenominators
import KltDP.Geometry.QuasicoherentOpenRestriction

/-!
# Actual finite generators and finite sections on original affine opens

Transport a finite original Over generating family through the proved
open-subscheme equivalence and canonical affine chart. The actual affine
counit gives finite original sections. Smaller affine subopens retain the
original generating indices under the accepted nested-Over functor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineOpenFiniteGenerators

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction AffineModuleTilde AffineOpenModule

variable {X : Scheme.{u}} (M : X.Modules)

local instance originalSectionModule (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

/-- Original finite generating sections transported to the actual open scheme. -/
def generatingSectionsOnOpen (U : X.Opens) (G : (M.over U).GeneratingSections) :
    ((restriction U.ι).obj M).GeneratingSections :=
  (G.map (openToOverEquivalence U).inverse (overToOpenUnitIso U)).ofEpi
    (overToOpenRestrictionIso U M).hom

/-- The original finite index is preserved by the actual open comparison. -/
theorem generatingSectionsOnOpen_finite (U : X.Opens)
    (G : (M.over U).GeneratingSections) [Finite G.I] :
    Finite (generatingSectionsOnOpen M U G).I :=
  inferInstanceAs (Finite G.I)

private def canonicalAffineRestrictionIso {U : X.Opens} (hU : IsAffineOpen U) :
    (restriction U.ι ⋙ restriction hU.isoSpec.inv).obj M ≅
      (restriction hU.fromSpec).obj M :=
  (isoWhiskerRight (restrictionIsoPullback U.ι) (restriction hU.isoSpec.inv) ≪≫
    isoWhiskerLeft (schemeModulePullback U.ι) (restrictionIsoPullback hU.isoSpec.inv) ≪≫
    schemeModulePullbackCompIso hU.isoSpec.inv U.ι ≪≫
    (restrictionIsoPullback hU.fromSpec).symm).app M

/-- The same original finite family on the canonical affine spectrum. -/
def generatingSectionsOnFromSpec {U : X.Opens} (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) :
    ((restriction hU.fromSpec).obj M).GeneratingSections := by
  letI : PreservesColimitsOfSize.{u, u} (restriction hU.isoSpec.inv) :=
    (restrictionAdjunction hU.isoSpec.inv).leftAdjoint_preservesColimits
  exact ((generatingSectionsOnOpen M U G).map (restriction hU.isoSpec.inv)
    (restrictionUnitIso hU.isoSpec.inv).symm).ofEpi (canonicalAffineRestrictionIso M hU).hom

/-- Passing to the canonical affine spectrum retains the original finite index. -/
theorem generatingSectionsOnFromSpec_finite {U : X.Opens} (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [Finite G.I] :
    Finite (generatingSectionsOnFromSpec M hU G).I :=
  inferInstanceAs (Finite G.I)

/-- The canonical affine chart's actual global-section equivalence is linear
over the original ambient section ring. -/
def sectionsFromSpecLinearEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    sectionModule ((restriction hU.fromSpec).obj M) ⊤ ≃ₗ[Γ(X, U)]
      M.val.obj (op U) where
  toFun := sectionsOfImageEq hU.fromSpec M ⊤ U (fromSpec_image_top hU)
  invFun := (sectionsOfImageEq hU.fromSpec M ⊤ U (fromSpec_image_top hU)).symm
  left_inv := (sectionsOfImageEq hU.fromSpec M ⊤ U (fromSpec_image_top hU)).left_inv
  right_inv := (sectionsOfImageEq hU.fromSpec M ⊤ U (fromSpec_image_top hU)).right_inv
  map_add' := (sectionsOfImageEq hU.fromSpec M ⊤ U (fromSpec_image_top hU)).map_add
  map_smul' r t := by
    have h := sectionsOfImageEq_base_smul hU M ⊤ U (fromSpec_image_top hU) le_rfl r t
    have hr : X.presheaf.map (homOfLE (show U ≤ U from le_rfl)).op r = r := by
      change X.presheaf.map (𝟙 (op U)) r = r
      rw [CategoryTheory.Functor.map_id]
      rfl
    simpa only [hr] using h

/-- A finite actual Over generating family gives finite original sections
on that original affine open. -/
theorem sections_finite_of_over_generators [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [Finite G.I] :
    Module.Finite Γ(X, U) (M.val.obj (op U)) := by
  let N := (restriction hU.fromSpec).obj M
  let G' := generatingSectionsOnFromSpec M hU G
  letI : Finite G'.I := generatingSectionsOnFromSpec_finite M hU G
  letI : Module.Finite Γ(X, U) (sectionModule N ⊤) :=
    globalSections_finite_of_generatingSections N G'
  exact Module.Finite.equiv (sectionsFromSpecLinearEquiv M hU)

/-- Restrict an original Over generating family to a smaller original open. -/
def generatingSectionsOnSubopen {U V : X.Opens} (hVU : V ≤ U)
    (G : (M.over U).GeneratingSections) : (M.over V).GeneratingSections :=
  (G.map (_root_.SheafOfModules.overToSingleFunctor X.ringCatSheaf
      (Over.mk (homOfLE hVU)))
    (_root_.SheafOfModules.overToSingleUnitIso X.ringCatSheaf
      (Over.mk (homOfLE hVU)))).ofEpi
    (_root_.SheafOfModules.iteratedOverObjIso X.ringCatSheaf M
      (Over.mk (homOfLE hVU))).hom

/-- Every smaller affine subopen has finite original sections, with no
new finite family or local presentation assumed. -/
theorem sections_finite_of_over_generators_of_le [M.IsQuasicoherent]
    {U V : X.Opens} (hVU : V ≤ U) (hV : IsAffineOpen V)
    (G : (M.over U).GeneratingSections) [Finite G.I] :
    Module.Finite Γ(X, V) (M.val.obj (op V)) := by
  let G' := generatingSectionsOnSubopen M hVU G
  letI : Finite G'.I := inferInstanceAs (Finite G.I)
  exact sections_finite_of_over_generators M hV G'

end KltDP.Geometry.AffineOpenFiniteGenerators
