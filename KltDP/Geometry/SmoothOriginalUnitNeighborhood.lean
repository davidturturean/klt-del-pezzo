import KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra
import KltDP.Geometry.SmoothCurveCotangentInvertible
import KltDP.Geometry.TransitionUnitSheaf

/-!
# Actual smooth affine neighborhoods inside an original coefficient's unit locus

A principal refinement of the original smooth chart lies inside the
original nonvanishing open. Original restriction maps preserve the unit
coefficient and the standard-smooth dimension of the actual section ring.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SmoothOriginalUnitNeighborhood

open TransitionUnitGluing GluedAdjunctionBasicOpenAlgebra

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsSmoothOfRelativeDimension 2 f]

/-- The same point has an actual smooth affine subchart on which the
original restricted coefficient is a unit. -/
theorem exists_refined_unit (U : X.affineOpens) (s : Γ(X, U.1))
    (x : X) (hx : x ∈ X.basicOpen s) :
    ∃ V : X.affineOpens, ∃ hVU : V.1 ≤ U.1,
      x ∈ V.1 ∧ IsUnit (res X hVU s) ∧
      letI : Algebra k Γ(X, V.1) := GluedChartKaehlerPullback.chartAlgebra f V
      Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, V.1) := by
  obtain ⟨W, hW, hxW, hWsm⟩ :=
    SmoothCurveCotangent.exists_affine_standardSmoothOfRelativeDimension f 2 x
  let W' : X.affineOpens := ⟨W, hW⟩
  obtain ⟨r, hr, hxr⟩ := hW.exists_basicOpen_le ⟨x, hx⟩ hxW
  have hVU : (X.affineBasicOpen (U := W') r).1 ≤ U.1 := hr.trans (X.basicOpen_le s)
  refine ⟨X.affineBasicOpen (U := W') r, hVU, hxr, ?_, ?_⟩
  · have hunit : IsUnit (res X (X.basicOpen_le s) s) :=
      X.toRingedSpace.isUnit_res_basicOpen s
    simpa only [res_res] using hunit.map (res X hr)
  · letI : Algebra k Γ(X, W'.1) := GluedChartKaehlerPullback.chartAlgebra f W'
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, W'.1) := hWsm.toAlgebra
    exact ambient_standardSmooth f W' r

end KltDP.Geometry.SmoothOriginalUnitNeighborhood

#print axioms KltDP.Geometry.SmoothOriginalUnitNeighborhood.exists_refined_unit
