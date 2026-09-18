import KltDP.Geometry.ProperBirationalStructureSheaf
import KltDP.Geometry.ProperSteinConnected
import KltDP.Geometry.ActualExceptionalIncidence

/-!
# Connected original fibers from the actual proper birational morphism

The original pushforward structure-sheaf isomorphism is already proved
without a Stein premise. The selected full Stein factorization theorem
then gives connectedness after every original field-valued base change,
and hence connectedness and nonemptiness of every original point fiber.

This adapter explicitly uses the existing isolated literature declaration
`KltDP.Literature.Stacks.steinFactorization_noetherian_literal` through
`ProperSteinConnected`. It does not assert an ordinary-only connectedness
proof or the existence of a resolution. The support and graph modules
continue to expose their ordinary connected-fiber hypotheses separately.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry.ProperBirationalConnectedFibers

/-- The original proper birational morphism to an integral normal target
has connected fibers after every original field-valued base change. -/
theorem geometrically_connected
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X] [IsLocallyNoetherian X]
    (π : S ⟶ X) [IsProper π] (hbir : IsBirationalScheme π)
    (hnormal : IsNormalScheme X) :
    ∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ X),
      ConnectedSpace (pullback π q : Scheme.{u}) := by
  letI : IsIso π.c := ProperBirationalStructureSheaf.c_isIso π hbir hnormal
  exact ProperSteinConnected.geometrically_connected π

/-- Every original point fiber is connected and nonempty. -/
theorem pointFibers_connected
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X] [IsLocallyNoetherian X]
    (π : S ⟶ X) [IsProper π] (hbir : IsBirationalScheme π)
    (hnormal : IsNormalScheme X) (x : X) : IsConnected (π.base ⁻¹' {x}) := by
  letI : IsIso π.c := ProperBirationalStructureSheaf.c_isIso π hbir hnormal
  exact ProperSteinConnected.pointFibers_connected π x

/-- Connected original fibers are derived from the defining properties
of an actual resolution, with no replacement map or section algebra. -/
theorem resolution_pointFibers_connected
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (hπ : IsResolution S X π)
    (x : X.toScheme) : IsConnected (π.base ⁻¹' {x}) := by
  letI : IsProper π := hπ.isProper
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  exact pointFibers_connected π
    ((isBirational_iff_isBirationalScheme π).mp hπ.birational) X.normal x

/-- The graph built from all actual contracted primes has finitely many
components and bounds the number of actual singular points; the original
connected-fiber condition is now derived rather than supplied. -/
theorem singularPoints_card_le_graph_components
    {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (hπ : IsResolution S X π) :
    Finite (ActualExceptionalIncidence.graph π).ConnectedComponent ∧
      X.singularPoints.card ≤
        Nat.card (ActualExceptionalIncidence.graph π).ConnectedComponent :=
  ActualExceptionalIncidence.singularPoints_card_le_graph_components π hπ
    (resolution_pointFibers_connected π hπ)

end KltDP.Geometry.ProperBirationalConnectedFibers

#print axioms KltDP.Geometry.ProperBirationalConnectedFibers.geometrically_connected
#print axioms KltDP.Geometry.ProperBirationalConnectedFibers.singularPoints_card_le_graph_components
