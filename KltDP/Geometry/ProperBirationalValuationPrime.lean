import KltDP.Geometry.ProperBirationalCodimensionOne
import KltDP.Geometry.SurfacePrimeCurvePoints

/-!
# Detect original valuation points on a proper birational source surface

The target is any integral scheme. Its original codimension-one valuation
point lifts through the proved isomorphism neighborhood to an actual prime
curve on the source surface. The original stalk map is an isomorphism and
the image of the entire curve is the original point closure.

This composes the existing valuation-stalk spreading theorem, the original
isomorphism-open correspondence, and the proved surface point/curve
equivalence. No projectivity or normality of the target is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperBirationalValuationPrime

attribute [local instance] integralSchemeStalk_isDomain

/-- An actual valuation point of codimension one on any integral target
is detected by an actual source prime and the original stalk isomorphism. -/
theorem exists_prime_above_valuation_point
    {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) {X : Scheme.{u}} [IsIntegral X]
    (π : S.toScheme ⟶ X) [IsProper π] (hbir : IsBirationalScheme π)
    (x : CodimensionOnePoint X) [ValuationRing (X.presheaf.stalk x.val)] :
    ∃ D : S.PrimeCurve,
      π.base D.genericPoint = x.val ∧ IsIso (π.stalkMap D.genericPoint) ∧
      π.base '' (D : Set S.toScheme) = closure ({x.val} : Set X) := by
  obtain ⟨U, hxU, hπU⟩ :=
    ProperBirationalCodimensionOne.exists_isomorphism_open_at_valuation_stalk
      π hbir x.val
  letI : IsIso (π ∣_ U) := hπU
  let E := codimensionOneOverOpenEquiv π U
  let y : CodimensionOnePointInOpen U := ⟨x, hxU⟩
  let z := E.symm y
  have hz : π.base z.val.val = x.val := by
    calc
      π.base z.val.val = (E z).val.val :=
        (codimensionOneOverOpenEquiv_apply_val π U z).symm
      _ = y.val.val := congrArg (fun w : CodimensionOnePointInOpen U => w.val.val)
        (E.apply_symm_apply y)
      _ = x.val := rfl
  let D : S.PrimeCurve := S.codimensionOnePointToPrimeCurve z.val
  have hD : D.genericPoint = z.val.val :=
    S.codimensionOnePointToPrimeCurve_genericPoint z.val
  have hmap : π.base D.genericPoint = x.val := (congrArg π.base hD).trans hz
  refine ⟨D, hmap, ?_, ?_⟩
  · exact isIso_stalkMap_of_isIso_restrict π U D.genericPoint
      (by rw [hmap]; exact hxU)
  · rw [← D.closure_genericPoint,
      ← π.isClosedMap.closure_image_eq_of_continuous π.continuous,
      Set.image_singleton, hmap]

/-- Normality and local Noetherianity derive the valuation property at
the original codimension-one point, without requiring a projective target. -/
theorem exists_prime_above_normal_point
    {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (hnormal : IsNormalScheme X)
    (π : S.toScheme ⟶ X) [IsProper π] (hbir : IsBirationalScheme π)
    (x : CodimensionOnePoint X) :
    ∃ D : S.PrimeCurve,
      π.base D.genericPoint = x.val ∧ IsIso (π.stalkMap D.genericPoint) ∧
      π.base '' (D : Set S.toScheme) = closure ({x.val} : Set X) := by
  letI : IsDomain (X.presheaf.stalk x.val) := (hnormal x.val).1
  letI : IsDiscreteValuationRing (X.presheaf.stalk x.val) :=
    normalStalk_isDiscreteValuationRing_of_isLocallyNoetherian
      X hnormal x.val x.property
  exact exists_prime_above_valuation_point S π hbir x

end KltDP.Geometry.ProperBirationalValuationPrime

#check @KltDP.Geometry.ProperBirationalValuationPrime.exists_prime_above_valuation_point
#check @KltDP.Geometry.ProperBirationalValuationPrime.exists_prime_above_normal_point
#print axioms KltDP.Geometry.ProperBirationalValuationPrime.exists_prime_above_valuation_point
#print axioms KltDP.Geometry.ProperBirationalValuationPrime.exists_prime_above_normal_point
