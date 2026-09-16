import KltDP.Geometry.SurfaceHodgeIndexSource
import KltDP.Geometry.IntegralNumericalFiniteRank

/-!
# Full integral Num freeness and finite-generation source assessment

The raw assertion is the entire independent Num sentence of Hartshorne V,
Remark 1.9.1, p.364. Integral Num is the original integral Picard quotient.
Both freeness and finite generation are retained. No axiom occurs here.
The rational finite-dimensionality conclusion is separately proved from the
canonical rationalization of this exact quotient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.SurfaceRiemannRochSource

universe u

namespace KltDP.Geometry.SurfaceNumericalFinitenessSource

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The original prime-curve kernel is exactly the source all-divisor kernel. -/
theorem numericallyTrivial_iff_all_weil_pairings (p : X.toScheme.Pic) :
    X.NumericallyTrivial p ↔ ∀ E : X.WeilDivisor,
      X.picardPairing hregular p
        (cartierPicardClass X.toScheme ((X.regularCartierWeilEquiv hregular).symm E)) = 0 := by
  constructor
  · intro hp E
    rw [X.picardPairing_symm hregular]
    exact X.picardPairing_eq_zero_of_numericallyTrivial hregular _ p hp
  · intro hp C
    have hC := hp ((X.regularCartierWeilEquiv hregular) (X.primeCurveCartier hregular C))
    simpa only [AddEquiv.symm_apply_apply, X.picardPairing_primeCurveClass hregular] using hC

/-- The exact subgroup defining integral Num has the published numerical test. -/
theorem mem_integralNum_kernel_iff (p : Additive X.toScheme.Pic) :
    p ∈ X.numericallyTrivialSubgroup ↔ ∀ E : X.WeilDivisor,
      X.picardPairing hregular p.toMul
        (cartierPicardClass X.toScheme ((X.regularCartierWeilEquiv hregular).symm E)) = 0 :=
  (X.mem_numericallyTrivialSubgroup_iff p).trans
    (numericallyTrivial_iff_all_weil_pairings X hregular p.toMul)

/-- Both conclusions of the complete published integral Num assertion. -/
def RawStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
    (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
    (hdimension : topologicalKrullDim Y = 2)
    (hregular : ∀ y : Y, RegularPoint Y y),
    let X := sourceSurface Y f hIntegral hprojective hdimension hregular
    Module.Free ℤ X.IntegralNumericalClassGroup ∧
      Module.Finite ℤ X.IntegralNumericalClassGroup

include hregular

/-- Specialization preserves the original scheme, map, Picard group and quotient. -/
theorem integralNum_free_and_finite (raw : RawStatement.{u}) :
    Module.Free ℤ X.IntegralNumericalClassGroup ∧
      Module.Finite ℤ X.IntegralNumericalClassGroup :=
  raw k X.toScheme X.structureMorphism X.integral X.projective X.dimension_two hregular

/-- Actual rational numerical classes form a finite module after the source input. -/
theorem numericalClassGroup_finite (raw : RawStatement.{u}) :
    Module.Finite ℚ X.NumericalClassGroup := by
  letI := (integralNum_free_and_finite X hregular raw).2
  exact X.numericalClassGroup_finite_of_integralNum_finite

/-- The actual numerical space is finite dimensional; no alternate space is used. -/
theorem numericalClassGroup_finiteDimensional (raw : RawStatement.{u}) :
    FiniteDimensional ℚ X.NumericalClassGroup :=
  numericalClassGroup_finite X hregular raw

end KltDP.Geometry.SurfaceNumericalFinitenessSource

