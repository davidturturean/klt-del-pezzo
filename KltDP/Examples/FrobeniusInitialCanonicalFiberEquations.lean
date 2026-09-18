import KltDP.Examples.FrobeniusInitialCanonicalFiberPoint
import KltDP.Examples.FrobeniusInitialCanonicalFiberMaps
import KltDP.Examples.FrobeniusGraphPicardClassRulingDivisors

/-!
# Pulling back the original coordinate-point Cartier equations

The original polynomial-chart normalization identifies the actual point
ideal generator with the ordinary coordinate section. Its pulled regular
equations are therefore the existing ruling coordinate and one. Equality
on the two original ruling opens identifies the actual pulled Cartier
divisor with the infinity ruling plus the principal coordinate divisor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusInitialCanonicalFiberEquations

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusGraphPicardClassIntegral
open FrobeniusProjectiveCoordinateIdeal FrobeniusProjectiveCoordinateTransition
open FrobeniusGraphPicardClassRulingCoordinates FrobeniusGraphPicardClassChartSections
open FrobeniusGraphPicardClassRulingDivisors
open FrobeniusInitialCanonicalFiberPoint FrobeniusInitialCanonicalFiberMaps

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance fiberEquationProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance fiberEquationLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance fiberEquationChartNonempty (i : Fin 2) : Nonempty (chartOpen k i) :=
  ⟨⟨(rulingProjection (k := k) 0).base (genericPoint (projectiveProduct k)),
    rulingGeneric_mem 0 i⟩⟩

local instance fiberEquationFirstNonempty : Nonempty (firstOpen (k := k)) := by
  rw [firstOpen_eq]
  infer_instance

local instance fiberEquationGeneric (d : Fin 2) :
    GenericPointPreserving (rulingProjection (k := k) d) :=
  rulingProjection_genericPointPreserving d

/-- The original point-ideal section is the original left coordinate, transported
only along the equality of its two descriptions of the first open. -/
theorem firstSection_eq_coordinateRestriction :
    firstSection (k := k) =
      (projectiveSpace k 1).presheaf.map (homOfLE (firstOpen_eq (k := k)).le).op
        leftCoordinateSection := by
  apply ((polynomialChartMap k 0).appIso ⊤).commRingCatIsoToRingEquiv.injective
  change ((polynomialChartMap k 0).appIso ⊤).hom firstSection =
    ((polynomialChartMap k 0).appIso ⊤).hom
      ((projectiveSpace k 1).presheaf.map (homOfLE (firstOpen_eq (k := k)).le).op
        leftCoordinateSection)
  rw [firstSection, Iso.inv_hom_id_apply, Scheme.Hom.appIso_hom']
  have h := ConcreteCategory.congr_hom
    ((polynomialChartMap k 0).map_appLE
      ((polynomialChartMap k 0).preimage_image_eq ⊤).ge
      (homOfLE (firstOpen_eq (k := k)).le).op) (leftCoordinateSection (k := k))
  have hc : (polynomialChartMap k 0).appLE (chartOpen k 0) ⊤
      (polynomialChart_preimage_top 0) leftCoordinateSection =
        affineCoordinateEquation (k := k) := by
    simpa only [lineCoordinateSection_zero, affineCoordinateEquation] using
      polynomialChart_coordinate (k := k) 0
  exact (h.trans hc).symm

/-- The first actual point-Cartier equation has the original left-coordinate germ. -/
theorem coordinateFirstEquation_germ :
    ((coordinateFirstRegularChart (k := k)).chart.equation :
        (projectiveSpace k 1).functionField) =
      (projectiveSpace k 1).germToFunctionField (chartOpen k 0) leftCoordinateSection := by
  change (projectiveSpace k 1).germToFunctionField (firstOpen (k := k)) firstSection = _
  rw [firstSection_eq_coordinateRestriction]
  exact (projectiveSpace k 1).presheaf.germ_res_apply
    (homOfLE (firstOpen_eq (k := k)).le) (genericPoint (projectiveSpace k 1))
    (genericPoint_mem_nonempty_open (projectiveSpace k 1) (firstOpen (k := k))) _

/-- The same original chart, on the literally standard first open. -/
def coordinateLeftRegularChart :
    RegularCartierEquationChart (projectiveSpace k 1) (coordinateCartier (k := k)) :=
  RegularCartierEquationChart.restrict (projectiveSpace k 1) coordinateCartier
    coordinateFirstRegularChart (chartOpen k 0) (firstOpen_eq (k := k)).symm.le

/-- Pullback of the first original point equation is the existing ruling-coordinate unit. -/
theorem pulled_coordinateLeftEquation (d : Fin 2) :
    pulledEquation (rulingProjection (k := k) d) coordinateCartier coordinateLeftRegularChart =
      rulingCoordinateUnit d := by
  apply Units.ext
  rw [pulledEquation_val]
  change functionFieldMap (rulingProjection (k := k) d)
    ((coordinateFirstRegularChart (k := k)).chart.equation :
      (projectiveSpace k 1).functionField) = rulingLeft d
  rw [coordinateFirstEquation_germ, functionFieldMap_leftCoordinate]

/-- The original second point-Cartier equation is one. -/
theorem coordinateRightEquation_eq_one :
    (coordinateRightRegularChart (k := k)).chart.equation = 1 := by
  apply Units.ext
  change (projectiveSpace k 1).germToFunctionField (chartOpen k 1) 1 = 1
  exact map_one _

/-- Pullback retains that original unit equation. -/
theorem pulled_coordinateRightEquation (d : Fin 2) :
    pulledEquation (rulingProjection (k := k) d) coordinateCartier coordinateRightRegularChart =
      1 := by
  simp only [pulledEquation, coordinateRightEquation_eq_one, map_one]

/-- The actual pulled divisor has equation x or y on the first ruling open. -/
theorem pullback_coordinateCartier_restrict_left (d : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show rulingOpen (k := k) d 0 ≤ ⊤ from le_top)).op
        (pullbackDivisor (rulingProjection d) coordinateCartier coordinateCartier_hasRegularEquations) =
      cartierEquationClassHom (projectiveProduct k) (rulingOpen d 0)
        (Additive.ofMul (rulingCoordinateUnit d)) := by
  have h := pullbackDivisor_restrict (rulingProjection (k := k) d) coordinateCartier
    coordinateCartier_hasRegularEquations coordinateLeftRegularChart
  change (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show rulingOpen (k := k) d 0 ≤ ⊤ from le_top)).op
      (pullbackDivisor (rulingProjection d) coordinateCartier coordinateCartier_hasRegularEquations) =
    cartierEquationClassHom (projectiveProduct k) (rulingOpen d 0)
      (Additive.ofMul (pulledEquation (rulingProjection d) coordinateCartier
        coordinateLeftRegularChart)) at h
  rwa [pulled_coordinateLeftEquation] at h

/-- The actual pulled divisor has the unit equation on the second ruling open. -/
theorem pullback_coordinateCartier_restrict_right (d : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show rulingOpen (k := k) d 1 ≤ ⊤ from le_top)).op
        (pullbackDivisor (rulingProjection d) coordinateCartier coordinateCartier_hasRegularEquations) =
      0 := by
  have h := pullbackDivisor_restrict (rulingProjection (k := k) d) coordinateCartier
    coordinateCartier_hasRegularEquations coordinateRightRegularChart
  change (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show rulingOpen (k := k) d 1 ≤ ⊤ from le_top)).op
      (pullbackDivisor (rulingProjection d) coordinateCartier coordinateCartier_hasRegularEquations) =
    cartierEquationClassHom (projectiveProduct k) (rulingOpen d 1)
      (Additive.ofMul (pulledEquation (rulingProjection d) coordinateCartier
        coordinateRightRegularChart)) at h
  simpa only [pulled_coordinateRightEquation, ofMul_one, map_zero] using h

/-- The original pulled point divisor is the infinity ruling plus the principal
coordinate divisor, proved by equality on the actual two ruling opens. -/
theorem pullback_coordinateCartier_eq_ruling_add_principal (d : Fin 2) :
    pullbackDivisor (rulingProjection (k := k) d) coordinateCartier
        coordinateCartier_hasRegularEquations =
      rulingInfinityDivisor d + principalCartierDivisorHom (projectiveProduct k)
        (Additive.ofMul (rulingCoordinateUnit d)) := by
  have hcover : (⊤ : (projectiveProduct k).Opens) ≤
      ⨆ i : ULift.{u} (Fin 2), rulingOpen d i.down := by
    intro x _
    have hx : x ∈ ⨆ i : Fin 2, rulingOpen (k := k) d i := by
      rw [rulingOpen_cover]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩
  apply cartierDivisor_eq_of_restrict_eq (projectiveProduct k)
    (fun i : ULift.{u} (Fin 2) => rulingOpen d i.down) hcover
  rintro ⟨i⟩
  fin_cases i
  · refine (pullback_coordinateCartier_restrict_left (k := k) d).trans ?_
    rw [map_add,
      rulingInfinityDivisor_restrict, principalCartierDivisorHom,
      cartierEquationClassHom_restrict]
    change cartierEquationClassHom (projectiveProduct k) (rulingOpen d 0)
        (Additive.ofMul (rulingCoordinateUnit d)) =
      cartierEquationClassHom (projectiveProduct k) (rulingOpen d 0)
        (Additive.ofMul (1 : (projectiveProduct k).functionFieldˣ)) +
      cartierEquationClassHom (projectiveProduct k) (rulingOpen d 0)
        (Additive.ofMul (rulingCoordinateUnit d))
    rw [ofMul_one, map_zero, zero_add]
  · refine (pullback_coordinateCartier_restrict_right (k := k) d).trans ?_
    rw [map_add,
      rulingInfinityDivisor_restrict, principalCartierDivisorHom,
      cartierEquationClassHom_restrict]
    change 0 = cartierEquationClassHom (projectiveProduct k) (rulingOpen d 1)
        (Additive.ofMul ((rulingCoordinateUnit d)⁻¹)) +
      cartierEquationClassHom (projectiveProduct k) (rulingOpen d 1)
        (Additive.ofMul (rulingCoordinateUnit d))
    rw [ofMul_inv, map_neg, neg_add_cancel]

end KltDP.Examples.FrobeniusInitialCanonicalFiberEquations
