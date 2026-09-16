import KltDP.Examples.FrobeniusBlowupDifferentialMap
import KltDP.Geometry.AffineTopDifferentialFrame
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# The native Rees-chart coordinate wedge is an actual frame

The original chart field map is standard smooth of relative dimension two:
compose the two original polynomial constant maps, then the inverse of the
original polynomial chart isomorphism. The existing top-differential frame
theorem applies to this exact field algebra on the native Rees chart.

The native determinant functional already takes `dchartU ∧ dchartW` to one.
Its inverse is therefore scalar multiplication by that original wedge.
This proves native spanning and constructs the actual tilde-to-unit frame
with the original wedge mapping to one. The actual exterior differential
image has coefficient `chartU` in this proved native frame.

The original plane-to-chart algebra is unchanged. No global canonical
divisor, scalar-extension determinant comparison or numerical degree is
asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace KltDP.Examples.FrobeniusReesChartDifferentialFrame

open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupDifferentialMap
open KltDP.Geometry
open KltDP.Compatibility.PolynomialStandardSmooth

universe u

variable {k : Type u} [Field k]

/-- Reuse exactly the field algebra in the original differential-map leaf. -/
local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartFieldAlgebra

/-- Composition of the two actual polynomial constant maps has relative
dimension two, as a statement about the original ring homomorphism. -/
theorem planeConstants_standardSmooth :
    RingHom.IsStandardSmoothOfRelativeDimension 2 (planeConstants (k := k)) :=
  (polynomialC_standardSmooth (Polynomial k)).comp (polynomialC_standardSmooth k)

/-- The original field map is the original polynomial constants map
followed by the original inverse chart presentation. -/
theorem inverseChartPolynomialEquiv_comp_planeConstants :
    (chartPolynomialEquiv (k := k)).symm.toRingHom.comp planeConstants =
      chartConstants (centerU (k := k)) := by
  apply RingHom.ext
  intro r
  exact (chartPolynomialAlgEquiv (k := k)).symm.commutes r

/-- The native chart is standard smooth of relative dimension two over
its exact original field algebra, without a rank or frame premise. -/
theorem chart_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 2 k (reesChartRing k) := by
  have h : RingHom.IsStandardSmoothOfRelativeDimension 2
      ((chartPolynomialEquiv (k := k)).symm.toRingHom.comp planeConstants) :=
    (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (chartPolynomialEquiv (k := k)).symm).comp planeConstants_standardSmooth
  rw [inverseChartPolynomialEquiv_comp_planeConstants] at h
  exact h

private theorem frameInverseIdentities {A M : Type u}
    [CommRing A] [AddCommGroup M] [Module A M]
    (e : M ≃ₗ[A] A) (F : M →ₗ[A] A) (w : M) (hw : F w = 1) :
    F.comp (LinearMap.toSpanSingleton A M w) = LinearMap.id ∧
      (LinearMap.toSpanSingleton A M w).comp F = LinearMap.id := by
  have hswap (x y : M) : e x • y = e y • x := by
    apply e.injective
    simp only [LinearEquiv.map_smul, smul_eq_mul]
    exact mul_comm _ _
  constructor
  · apply LinearMap.ext
    intro a
    change F (a • w) = a
    rw [LinearMap.map_smul, hw, smul_eq_mul, mul_one]
  · apply LinearMap.ext
    intro x
    change F x • w = x
    apply e.injective
    rw [LinearEquiv.map_smul, smul_eq_mul]
    calc
      F x * e w = e w * F x := mul_comm _ _
      _ = e x := by
        have hx := congrArg F (hswap w x)
        simpa only [LinearMap.map_smul, hw, smul_eq_mul, mul_one] using hx

/-- The native determinant functional gives the actual frame coordinates;
its inverse is scalar multiplication by the original chart coordinate wedge. -/
def chartTopDifferentialEquiv :
    (⋀[reesChartRing k]^2 (ChartDifferential k)) ≃ₗ[reesChartRing k] reesChartRing k := by
  letI := chart_standardSmooth (k := k)
  let e : (⋀[reesChartRing k]^2 (ChartDifferential k)) ≃ₗ[reesChartRing k] reesChartRing k :=
    AffineTopDifferentialFrame.standardSmoothTopDifferentialEquiv k (reesChartRing k)
  let F : (⋀[reesChartRing k]^2 (ChartDifferential k)) →ₗ[reesChartRing k] reesChartRing k :=
    chartTopFormEvaluator (k := k)
  let w : ⋀[reesChartRing k]^2 (ChartDifferential k) := chartCoordinateTopForm (k := k)
  let G : reesChartRing k →ₗ[reesChartRing k] (⋀[reesChartRing k]^2 (ChartDifferential k)) :=
    LinearMap.toSpanSingleton (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k)) w
  have hw : F w = 1 := chartTopFormEvaluator_coordinateTopForm (k := k)
  have h := frameInverseIdentities (A := reesChartRing k)
    (M := ⋀[reesChartRing k]^2 (ChartDifferential k)) e F w hw
  exact LinearEquiv.ofLinear F G h.1 h.2

theorem chartTopDifferentialEquiv_apply
    (ω : ⋀[reesChartRing k]^2 (ChartDifferential k)) :
    chartTopDifferentialEquiv (k := k) ω = chartTopFormEvaluator (k := k) ω := rfl

theorem chartTopDifferentialEquiv_symm_apply (a : reesChartRing k) :
    (chartTopDifferentialEquiv (k := k)).symm a =
      a • chartCoordinateTopForm (k := k) := rfl

/-- Every native top differential is its actual determinant coefficient
times the original native coordinate wedge. -/
theorem chartCoordinateTopForm_expansion
    (ω : ⋀[reesChartRing k]^2 (ChartDifferential k)) :
    chartTopFormEvaluator (k := k) ω • chartCoordinateTopForm (k := k) = ω :=
  (chartTopDifferentialEquiv (k := k)).symm_apply_apply ω

theorem chartCoordinateTopForm_spans :
    Submodule.span (reesChartRing k) {chartCoordinateTopForm (k := k)} = ⊤ := by
  apply top_unique
  intro ω _
  exact Submodule.mem_span_singleton.mpr
    ⟨chartTopFormEvaluator (k := k) ω, chartCoordinateTopForm_expansion (k := k) ω⟩

/-- The actual exterior differential image has the original exceptional
coordinate in the proved native frame. -/
theorem chartTopDifferentialEquiv_differentialImage :
    chartTopDifferentialEquiv (k := k)
        (chartTopDifferentialMap (k := k) (scalarExtendedCoordinateTopForm (k := k))) =
      chartU (k := k) :=
  chartJacobianCoordinateMap_coordinate (k := k)

/-- The native frame induces an isomorphism of the actual tilde sheaf
with the actual structure-sheaf unit on the original Rees chart. -/
def chartTopDifferentialSheafIso :
    (ModuleCat.of (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k))).tilde ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of (reesChartRing k))).ringCatSheaf :=
  AffineModuleTilde.linearEquivIso (R := reesChartRing k)
    (M := ModuleCat.of (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k)))
    (N := ModuleCat.of (reesChartRing k) (reesChartRing k))
    (chartTopDifferentialEquiv (k := k)) ≪≫ AffineModuleTilde.unitIso (reesChartRing k)

/-- Canonical sections keep their original determinant coordinate. -/
theorem chartTopDifferentialSheafIso_hom_toOpen
    (U : Opens (PrimeSpectrum (reesChartRing k)))
    (ω : ⋀[reesChartRing k]^2 (ChartDifferential k)) :
    (chartTopDifferentialSheafIso (k := k)).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k))) U ω) =
      (AffineModuleTilde.unitIso (reesChartRing k)).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen (ModuleCat.of (reesChartRing k) (reesChartRing k)) U
          (chartTopFormEvaluator (k := k) ω)) := by
  change (AffineModuleTilde.unitIso (reesChartRing k)).hom.val.app (op U)
      ((AffineModuleTilde.map (R := reesChartRing k)
        (M := ModuleCat.of (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k)))
        (N := ModuleCat.of (reesChartRing k) (reesChartRing k))
        (chartTopDifferentialEquiv (k := k)).toModuleIso.hom).val.app (op U)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k))) U ω)) = _
  exact congrArg ((AffineModuleTilde.unitIso (reesChartRing k)).hom.val.app (op U))
    (AffineModuleTilde.map_app_toOpen (R := reesChartRing k)
      (M := ModuleCat.of (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k)))
      (N := ModuleCat.of (reesChartRing k) (reesChartRing k))
      (chartTopDifferentialEquiv (k := k)).toModuleIso.hom U ω)

/-- The native frame coefficient is preserved at every prime-localization fiber. -/
theorem chartTopDifferentialSheafIso_hom_toOpen_val
    (U : Opens (PrimeSpectrum (reesChartRing k)))
    (ω : ⋀[reesChartRing k]^2 (ChartDifferential k)) (p : U) :
    ((chartTopDifferentialSheafIso (k := k)).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k))) U ω)).val p =
      algebraMap (reesChartRing k) (Localization.AtPrime p.val.asIdeal)
        (chartTopFormEvaluator (k := k) ω) := by
  rw [chartTopDifferentialSheafIso_hom_toOpen, AffineModuleTilde.unitIso_hom_app_val]
  exact AffineModuleTilde.unitFiberEquiv_mkLinearMap
    (reesChartRing k) p.val (chartTopFormEvaluator (k := k) ω)

/-- The original native coordinate wedge is the actual unit section in this frame. -/
theorem chartTopDifferentialSheafIso_hom_coordinateTopForm
    (U : Opens (PrimeSpectrum (reesChartRing k))) :
    (chartTopDifferentialSheafIso (k := k)).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k))) U
          (chartCoordinateTopForm (k := k))) =
      (1 : Γ(Spec (CommRingCat.of (reesChartRing k)), U)) := by
  apply Subtype.ext
  funext p
  simpa only [chartTopFormEvaluator_coordinateTopForm, map_one] using
    chartTopDifferentialSheafIso_hom_toOpen_val U (chartCoordinateTopForm (k := k)) p

end KltDP.Examples.FrobeniusReesChartDifferentialFrame
