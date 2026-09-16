import KltDP.Geometry.GluedConormalTildeDualChart
import KltDP.Geometry.GluedConormalEquationIndependence

/-!
# The actual global normal chart map is independent of the regular equation

Both original comparisons entering the normal chart map have proved
equation independence. Their composite into the pullback of the actual
global sheaf dual therefore has the same independence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.GluedConormalNormalEquationIndependence

/-- The original normal tilde chart map to the actual global conormal dual
is unchanged when the regular principal equation is changed. -/
theorem chartIso_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens)
    (d e : Γ(X, U.1)) (hUd : I.ideal U = Ideal.span {d})
    (hd : d ∈ nonZeroDivisors Γ(X, U.1)) (hUe : I.ideal U = Ideal.span {e})
    (he : e ∈ nonZeroDivisors Γ(X, U.1)) :
    GluedConormalTildeDualChart.chartIso I hI U d hUd hd =
      GluedConormalTildeDualChart.chartIso I hI U e hUe he := by
  unfold GluedConormalTildeDualChart.chartIso
  rw [PrincipalConormalTildeDual.iso_eq (I.ideal U)
    (gluedAffineIdealEquation I U d hUd) hUd.symm hd
    (gluedAffineIdealEquation I U e hUe) hUe.symm he]
  rw [GluedConormalEquationIndependence.tildePullbackIso_eq I U d e hUd hd hUe he]

end KltDP.Geometry.GluedConormalNormalEquationIndependence
