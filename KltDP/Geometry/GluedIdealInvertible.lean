import KltDP.Geometry.GluedIdealKernelTrivialization
import KltDP.Geometry.SchemeKernelRestriction
import KltDP.Geometry.ModuleOpenOver

/-!
# Global kernel and conormal line sheaves from actual regular equations

For the actual closed scheme glued from ideal-sheaf data, regular
principal equations on affine neighborhoods give actual global locally
free rank-one kernel and conormal sheaves. The proof transports the
constructed quotient-chart trivializations through the proved actual
restriction comparisons and the actual opens/over-site comparison.

The premise is only the original ideal's local regular equations. Neither
invertibility nor any desired sheaf isomorphism is a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Actual regular equations for the original ideal on affine neighborhoods. -/
def IdealLocallyPrincipalRegular : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ d : Γ(X, U.1),
    I.ideal U = Ideal.span {d} ∧ d ∈ nonZeroDivisors Γ(X, U.1)

variable (hI : IdealLocallyPrincipalRegular I)

include hI in
/-- The actual global structural kernel is locally free of rank one,
by its proved actual quotient-chart trivializations. -/
theorem gluedKernel_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf)
      (schemeKernelIdeal I.gluedTo) := by
  apply isInvertible_of_openCharts
  intro x
  obtain ⟨U, hx, d, hEq, hregular⟩ := hI x
  exact ⟨U.1, hx, ⟨gluedAffineKernelIso I U d hEq hregular ≪≫
    (schemeKernelRestrictionIso I.gluedTo U.1).symm⟩⟩

include hI in
/-- The actual global conormal sheaf is locally free of rank one on the
actual closed scheme. Its neighborhoods are the inverse images of the
proved regular-equation charts, with the actual conormal comparison. -/
theorem gluedConormal_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := I.glueData.glued.ringCatSheaf)
      (schemeConormalSheaf I.gluedTo) := by
  apply isInvertible_of_openCharts
  intro x
  obtain ⟨U, hx, d, hEq, hregular⟩ := hI (I.gluedTo.base x)
  exact ⟨I.gluedTo ⁻¹ᵁ U.1, hx, ⟨gluedAffineConormalIso I U d hEq hregular ≪≫
    (schemeConormalRestrictionIso I.gluedTo U.1).symm⟩⟩

/-- The actual ideal line sheaf, with its derived local rank-one property. -/
def gluedKernelLine : InvertibleSheaf X :=
  ⟨schemeKernelIdeal I.gluedTo, gluedKernel_isInvertible I hI⟩

/-- The actual conormal line sheaf on the glued closed scheme. -/
def gluedConormalLine : InvertibleSheaf I.glueData.glued :=
  ⟨schemeConormalSheaf I.gluedTo, gluedConormal_isInvertible I hI⟩

end KltDP.Geometry
