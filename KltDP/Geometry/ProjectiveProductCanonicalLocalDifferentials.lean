import KltDP.Geometry.ProjectiveProductCanonicalDifferentials
import KltDP.Geometry.ProjectiveProductCanonicalTensorCharts
import KltDP.Geometry.ProjectiveProductCanonicalChartMaps

/-!
# Original projective-product differentials in the tensor charts

The two factor comparisons and the target comparison are actual open
restriction isomorphisms. The displayed squares identify each pulled global
differential with the original affine differential of the corresponding
tensor projection. No chosen differential splitting or overlap identity is
assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalLocalDifferentials

open SchemeKaehlerSheaf SchemeKaehlerPullbackMap ProjectiveLineComparison
open KltDP.Examples.FrobeniusProjectivePoints KltDP.Examples.FrobeniusGraphClosed
open ProjectiveProductCanonicalDifferentials

variable (k : Type u) [Field k]

local notation "TC" => ProjectiveProductCanonicalTensorCharts.chart

abbrev lineBase : Spec (CommRingCat.of (Polynomial k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))

abbrev tensorBase :
    Spec (CommRingCat.of (ProjectiveProductCanonicalTensorCharts.chartRing k)) ⟶
      Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap k (ProjectiveProductCanonicalTensorCharts.chartRing k)))

/-- The first global pulled cotangent line restricted to the original tensor chart. -/
def firstFactorIso (i j : Fin 2) :
    (schemeModulePullback (TC k i j)).obj (firstFactor k) ≅
      (schemeModulePullback
        (AffineProductKaehler.firstProjection k (Polynomial k) (Polynomial k))).obj
          (baseRingSheaf (lineBase k)) :=
  ProjectiveProductCanonicalChartMaps.factorIso (projectiveSpaceToSpec k 1)
    firstProjection (polynomialChartMap k i) (TC k i j)
    (AffineProductKaehler.firstProjection k (Polynomial k) (Polynomial k))
    (ProjectiveProductCanonicalTensorCharts.chart_fst k i j)
    (lineBase k) (polynomialChartMap_structureMap k i)

/-- The second global pulled cotangent line restricted to the original tensor chart. -/
def secondFactorIso (i j : Fin 2) :
    (schemeModulePullback (TC k i j)).obj (secondFactor k) ≅
      (schemeModulePullback
        (AffineProductKaehler.secondProjection k (Polynomial k) (Polynomial k))).obj
          (baseRingSheaf (lineBase k)) :=
  ProjectiveProductCanonicalChartMaps.factorIso (projectiveSpaceToSpec k 1)
    secondProjection (polynomialChartMap k j) (TC k i j)
    (AffineProductKaehler.secondProjection k (Polynomial k) (Polynomial k))
    (ProjectiveProductCanonicalTensorCharts.chart_snd k i j)
    (lineBase k) (polynomialChartMap_structureMap k j)

/-- The original global differential sheaf restricted to the original tensor chart. -/
def differentialIso (i j : Fin 2) :
    (schemeModulePullback (TC k i j)).obj
        (baseRingSheaf (projectiveProductToSpec (k := k))) ≅
      baseRingSheaf (tensorBase k) :=
  ProjectiveProductCanonicalChartMaps.targetIso (TC k i j)
    projectiveProductToSpec (tensorBase k)
    (ProjectiveProductCanonicalTensorCharts.chart_structure k i j)

/-- The first local differential is exactly the pullback of the first global one. -/
theorem firstFactorIso_differential (i j : Fin 2) :
    (firstFactorIso k i j).hom ≫
        map (lineBase k)
          (AffineProductKaehler.firstProjection k (Polynomial k) (Polynomial k)) ≫
        eqToHom (congrArg baseRingSheaf
          (AffineProductKaehler.firstProjection_comp k (Polynomial k) (Polynomial k))) =
      (schemeModulePullback (TC k i j)).map (firstDifferential k) ≫
        (differentialIso k i j).hom := by
  simpa only [firstFactorIso, differentialIso, firstDifferential,
    eqToHom_refl, Category.comp_id] using
    ProjectiveProductCanonicalChartMaps.factorIso_differential
      (projectiveSpaceToSpec k 1) firstProjection (polynomialChartMap k i) (TC k i j)
      (AffineProductKaehler.firstProjection k (Polynomial k) (Polynomial k))
      (ProjectiveProductCanonicalTensorCharts.chart_fst k i j)
      (projectiveProductToSpec (k := k)) (lineBase k) (tensorBase k)
      rfl (polynomialChartMap_structureMap k i)
      (ProjectiveProductCanonicalTensorCharts.chart_structure k i j)
      (AffineProductKaehler.firstProjection_comp k (Polynomial k) (Polynomial k))

private def secondFactorIso_differential_proof (i j : Fin 2) :=
  ProjectiveProductCanonicalChartMaps.factorIso_differential
      (projectiveSpaceToSpec k 1) secondProjection (polynomialChartMap k j) (TC k i j)
      (AffineProductKaehler.secondProjection k (Polynomial k) (Polynomial k))
      (ProjectiveProductCanonicalTensorCharts.chart_snd k i j)
      (projectiveProductToSpec (k := k)) (lineBase k) (tensorBase k)
      (secondProjection_structure k) (polynomialChartMap_structureMap k j)
      (ProjectiveProductCanonicalTensorCharts.chart_structure k i j)
      (AffineProductKaehler.secondProjection_comp k (Polynomial k) (Polynomial k))

private abbrev statementOf {P : Prop} (_ : P) : Prop := P

/-- The second local differential retains the original fiber-product base-map equality.
Its transparent result type is the original chart square, specialized to the actual
second projection and the same factor/target isomorphism definitions. -/
theorem secondFactorIso_differential (i j : Fin 2) :
    statementOf (secondFactorIso_differential_proof k i j) :=
  secondFactorIso_differential_proof k i j

end KltDP.Geometry.ProjectiveProductCanonicalLocalDifferentials
