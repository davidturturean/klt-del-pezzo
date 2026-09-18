import KltDP.Geometry.QuadraticPushforwardCoefficientMaps
import KltDP.Geometry.SchemeModuleHomOnBasis

/-!
# Global coefficient projections on the original quadratic cover

The root coefficient transforms by the inverse of the original line's
transition functions. Actual matching sections therefore give the second
projection. The proved basis descent then constructs both global module
maps from the original cover, retaining their exact chart values.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticTransitionCocycle

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- The actual matching-section module for inverse original transition units. -/
abbrev inverseTransitionModule : X.Modules :=
  moduleSheaf X D.opens (inverseUnits X D.opens D.units)

/-- The original root coefficient expressed as an actual matching section. -/
def inverseCoordinate (i : ι) [Nontrivial Γ(X, D.opens i)] :
    D.pushforwardUnit.val.obj (op (D.opens i)) →ₗ[Γ(X, D.opens i)]
      D.inverseTransitionModule.val.obj (op (D.opens i)) :=
  ((trivialization X D.opens (inverseUnits X D.opens D.units)
    (inverseUnits_isCocycle X D.opens D.units D.cocycle) i
      (le_refl (D.opens i))).symm.toLinearMap).comp (D.rootCoordinate i)

/-- Inverse-coordinate matching sections commute with actual restriction. -/
theorem inverseCoordinate_restrict (i j : ι)
    [Nontrivial Γ(X, D.opens i)] [Nontrivial Γ(X, D.opens j)]
    (hij : D.opens i ≤ D.opens j)
    (s : D.pushforwardUnit.val.obj (op (D.opens j))) :
    D.inverseTransitionModule.val.map (homOfLE hij).op (D.inverseCoordinate j s) =
      D.inverseCoordinate i (D.pushforwardUnit.val.map (homOfLE hij).op s) := by
  let g := inverseUnits X D.opens D.units
  let hg := inverseUnits_isCocycle X D.opens D.units D.cocycle
  apply (trivialization X D.opens g hg j hij).injective
  change trivialization X D.opens g hg j hij
      (restrict X D.opens g hij
        ((trivialization X D.opens g hg j (le_refl (D.opens j))).symm
          (D.rootCoordinate j s))) =
    trivialization X D.opens g hg j hij
      ((trivialization X D.opens g hg i (le_refl (D.opens i))).symm
        (D.rootCoordinate i (D.pushforwardUnit.val.map (homOfLE hij).op s)))
  rw [trivialization_restrict, LinearEquiv.apply_symm_apply,
    trivialization_transition X D.opens g hg j i hij (le_refl (D.opens i)),
    LinearEquiv.apply_symm_apply, D.rootCoordinate_restrict i j hij,
    restrictedUnit_val]
  have hv : res X (le_inf hij (le_refl (D.opens i))) (g j i) *
      res X (le_inf hij (le_refl (D.opens i))) (D.units j i) = 1 := by
    dsimp only [g, inverseUnits]
    rw [← map_mul, Units.inv_mul, map_one]
  rw [mul_comm (res X hij (D.rootCoordinate j s)), ← mul_assoc, hv, one_mul]

variable {κ : Type u} (a : κ → ι)
  (hB : Opens.IsBasis (Set.range (fun i => D.opens (a i))))
  [∀ i, Nontrivial Γ(X, D.opens (a i))]

/-- The constant coefficient descends to the original structure sheaf. -/
def constantProjection : D.pushforwardUnit ⟶ _root_.SheafOfModules.unit X.ringCatSheaf :=
  SchemeModuleHomOnBasis.morphism D.pushforwardUnit
    (_root_.SheafOfModules.unit X.ringCatSheaf) (fun i => D.opens (a i)) hB
    (fun i => D.constantCoordinate (a i))
    (fun i j hij s => (D.constantCoordinate_restrict (a j) (a i) hij s).symm)

/-- The root coefficient descends to the actual inverse-transition module. -/
def inverseProjection : D.pushforwardUnit ⟶ D.inverseTransitionModule :=
  SchemeModuleHomOnBasis.morphism D.pushforwardUnit D.inverseTransitionModule
    (fun i => D.opens (a i)) hB (fun i => D.inverseCoordinate (a i))
    (fun i j hij s => D.inverseCoordinate_restrict (a j) (a i) hij s)

theorem constantProjection_app (i : κ) (s : D.pushforwardUnit.val.obj (op (D.opens (a i)))) :
    (D.constantProjection a hB).val.app (op (D.opens (a i))) s =
      D.constantCoordinate (a i) s :=
  SchemeModuleHomOnBasis.morphism_app D.pushforwardUnit
    (_root_.SheafOfModules.unit X.ringCatSheaf) (fun j => D.opens (a j)) hB
    (fun j => D.constantCoordinate (a j))
    (fun j l h s => (D.constantCoordinate_restrict (a l) (a j) h s).symm) i s

theorem inverseProjection_app (i : κ) (s : D.pushforwardUnit.val.obj (op (D.opens (a i)))) :
    (D.inverseProjection a hB).val.app (op (D.opens (a i))) s =
      D.inverseCoordinate (a i) s :=
  SchemeModuleHomOnBasis.morphism_app D.pushforwardUnit D.inverseTransitionModule
    (fun j => D.opens (a j)) hB (fun j => D.inverseCoordinate (a j))
    (fun j l h s => D.inverseCoordinate_restrict (a l) (a j) h s) i s

end KltDP.Geometry.QuadraticCoverAtlas.Data

#check @KltDP.Geometry.QuadraticCoverAtlas.Data.inverseProjection
#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.inverseProjection
