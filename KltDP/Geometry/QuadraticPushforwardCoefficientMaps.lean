import KltDP.Geometry.QuadraticAtlasPushforwardScalars
import KltDP.Geometry.QuadraticCoverCoefficientTransport
import KltDP.Geometry.TransitionUnitInverse

/-!
# Actual linear coefficient maps on the quadratic pushforward

The inverse-image section comparison retains the original scalar action.
Taking its two coordinates therefore gives actual linear maps. Their
restriction equations are proved from the original nested frame maps;
the root equation retains the original transition unit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover QuadraticTransitionCocycle

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The constant coordinate of the original pushforward module on a chart. -/
def constantCoordinate (i : ι) [Nontrivial Γ(X, D.opens i)] :
    (D.pushforwardUnit).val.obj (op (D.opens i)) →ₗ[Γ(X, D.opens i)] Γ(X, D.opens i) :=
  (constantCoeff (res X (le_refl (D.opens i)) (D.sections i))).comp
    (D.pushforwardChartLinearEquiv i).toLinearMap

/-- The root coordinate of the original pushforward module on a chart. -/
def rootCoordinate (i : ι) [Nontrivial Γ(X, D.opens i)] :
    (D.pushforwardUnit).val.obj (op (D.opens i)) →ₗ[Γ(X, D.opens i)] Γ(X, D.opens i) :=
  (rootCoeff (res X (le_refl (D.opens i)) (D.sections i))).comp
    (D.pushforwardChartLinearEquiv i).toLinearMap

/-- Constant coordinates commute with the original module restrictions. -/
theorem constantCoordinate_restrict (i j : ι)
    [Nontrivial Γ(X, D.opens i)] [Nontrivial Γ(X, D.opens j)]
    (hij : D.opens i ≤ D.opens j)
    (s : (D.pushforwardUnit).val.obj (op (D.opens j))) :
    D.constantCoordinate i ((D.pushforwardUnit).val.map (homOfLE hij).op s) =
      res X hij (D.constantCoordinate j s) := by
  have h := congrArg (constantCoeff (res X (le_refl (D.opens i)) (D.sections i)))
    (D.pushforwardChartAlgebraIso_restrict i j hij s)
  change constantCoeff (res X (le_refl (D.opens i)) (D.sections i))
      ((D.pushforwardChartAlgebraIso i).hom
        (res D.scheme (D.morphism.preimage_le_preimage_of_le hij) s)) =
    res X hij (constantCoeff (res X (le_refl (D.opens j)) (D.sections j))
      ((D.pushforwardChartAlgebraIso j).hom s))
  simpa only [map, localMap, mappedRescaleMap, Spec.preimage_map, CommRingCat.hom_ofHom,
    constantCoeff_mappedRescaleHom] using h

/-- The root-coordinate restriction retains the actual frame-change unit. -/
theorem rootCoordinate_restrict (i j : ι)
    [Nontrivial Γ(X, D.opens i)] [Nontrivial Γ(X, D.opens j)]
    (hij : D.opens i ≤ D.opens j)
    (s : (D.pushforwardUnit).val.obj (op (D.opens j))) :
    D.rootCoordinate i ((D.pushforwardUnit).val.map (homOfLE hij).op s) =
      res X hij (D.rootCoordinate j s) *
        (restrictedUnit X D.opens D.units hij (le_refl (D.opens i)) : Γ(X, D.opens i)) := by
  have h := congrArg (rootCoeff (res X (le_refl (D.opens i)) (D.sections i)))
    (D.pushforwardChartAlgebraIso_restrict i j hij s)
  change rootCoeff (res X (le_refl (D.opens i)) (D.sections i))
      ((D.pushforwardChartAlgebraIso i).hom
        (res D.scheme (D.morphism.preimage_le_preimage_of_le hij) s)) =
    res X hij (rootCoeff (res X (le_refl (D.opens j)) (D.sections j))
      ((D.pushforwardChartAlgebraIso j).hom s)) * _
  simpa only [map, localMap, mappedRescaleMap, Spec.preimage_map, CommRingCat.hom_ofHom,
    rootCoeff_mappedRescaleHom] using h

/-- Both original coefficients together are an actual linear equivalence. -/
def coefficientPairEquiv (i : ι) [Nontrivial Γ(X, D.opens i)] :
    (D.pushforwardUnit).val.obj (op (D.opens i)) ≃ₗ[Γ(X, D.opens i)]
      Γ(X, D.opens i) × Γ(X, D.opens i) :=
  (D.pushforwardChartLinearEquiv i).trans
    (coordinatesEquiv (res X (le_refl (D.opens i)) (D.sections i)))

theorem coefficientPairEquiv_apply (i : ι) [Nontrivial Γ(X, D.opens i)]
    (s : (D.pushforwardUnit).val.obj (op (D.opens i))) :
    D.coefficientPairEquiv i s = (D.constantCoordinate i s, D.rootCoordinate i s) := rfl

end KltDP.Geometry.QuadraticCoverAtlas.Data

#check @KltDP.Geometry.QuadraticCoverAtlas.Data.coefficientPairEquiv
#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.coefficientPairEquiv
