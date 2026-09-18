import KltDP.Geometry.IntegralFiniteTypeRegularLocus
import KltDP.Geometry.SmoothFieldRegularPoints
import KltDP.Geometry.FiniteTypeNoetherian
import Mathlib.Topology.JacobsonSpace

/-!
# All actual stalks of a smooth integral surface are regular

The accepted closed-point theorem supplies regularity at every closed
point. The actual regular locus is open by field-J2 and the integral
affine-localization comparison. A nonempty closed singular locus on the
original Jacobson scheme would contain a closed point, a contradiction.
No normality is assumed or used to supply source regularity.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace KltDP.Geometry

/-- On a Jacobson scheme with open regular locus, regularity of all
closed points implies regularity at every original scheme point. -/
theorem regularPoints_of_closedPoints_regular_of_isOpen_regularLocus
    (X : Scheme.{u}) [JacobsonSpace X] (hopen : IsOpen (regularLocus X))
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) → RegularPoint X x) :
    ∀ x : X, RegularPoint X x := by
  intro x
  by_contra hx
  have hsing : (singularLocus X).Nonempty := ⟨x, hx⟩
  have hsingClosed : IsClosed (singularLocus X) :=
    (isClosed_singularLocus_iff_isOpen_regularLocus X).mpr hopen
  obtain ⟨y, hy, hyclosed⟩ :=
    nonempty_inter_closedPoints hsing hsingClosed.isLocallyClosed
  exact hy (hclosed y hyclosed)

namespace SmoothFieldRegularPoints

/-- Smoothness of the original map to an algebraically closed field
proves regularity of every actual stalk in dimension at most two.
Noetherianity and the Jacobson property are derived from that same map. -/
theorem regularPoints_of_isSmooth_of_dimension_le_two
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsSmooth f]
    (hdim : topologicalKrullDim Y ≤ 2) : ∀ x : Y, RegularPoint Y x := by
  letI : LocallyOfFiniteType f := {
    finiteType_of_affine_subset := fun U V e =>
      RingHom.FiniteType.of_finitePresentation
        (LocallyOfFinitePresentation.finitePresentation_of_affine_subset
          (f := f) U V e) }
  letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_locallyOfFiniteType_toSpec f
  letI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
  apply regularPoints_of_closedPoints_regular_of_isOpen_regularLocus Y
    (integralLocallyFiniteType_regularLocus_isOpen f hdim)
  intro x hx
  exact regularPoint_of_isSmooth_of_isClosed' f
    (fun y => isNoetherianRing_stalk_of_isLocallyNoetherian Y y) hdim x hx

end SmoothFieldRegularPoints

end KltDP.Geometry
