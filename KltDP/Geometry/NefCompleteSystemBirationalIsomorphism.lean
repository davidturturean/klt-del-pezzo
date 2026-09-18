import KltDP.Geometry.CompleteSystemBirationalIsomorphism
import KltDP.Geometry.NefTwistedMaps
import KltDP.Geometry.ProjectiveEmbeddingLinearSystem

/-!
# Eventual complete-system birationality of the original nef line after an isomorphism

Original surface projectivity supplies a fixed actual embedding tuple.
The existing nef positive-square theorem gives actual nonzero maps from
that fixed line to every sufficiently large original power. Pulling this
data along the original scheme isomorphism proves the exact eventual
complete-system predicate there. All canonical and regularity hypotheses
stay on the original surface. The existing private RR dependency remains
unaccepted; this module introduces no literature admission.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.SurfaceRiemannRochSource

universe u

namespace KltDP.Geometry.NefCompleteSystemBirationalIsomorphism

/-- The actual pulled nef positive-square line has birational complete
systems for every sufficiently large power on any original isomorphic source. -/
theorem eventuallyBirational_pullback_of_isCanonical
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    (K : X.WeilDivisor) (hK : IsCanonical X hregular K)
    (A : InvertibleSheaf X.toScheme) (hA : Positivity.IsNef X.structureMorphism A)
    (hpositive : 0 < X.selfIntersection hregular A)
    {Y : Scheme.{u}} (j : Y ⟶ X.toScheme) [IsIso j] :
    letI : IsIntegral Y := IsomorphismPullbackSubsystem.source_isIntegral j
    letI : IsProper X.structureMorphism := X.projective.isProper
    letI : IsProper (j ≫ X.structureMorphism) := inferInstance
    KeelCompleteSystem.EventuallyBirational (j ≫ X.structureMorphism)
      (pullbackInvertibleSheaf j A) := by
  letI : IsProper X.structureMorphism := X.projective.isProper
  obtain ⟨H, m, s, hcover, hclosed⟩ := X.projective.exists_closedImmersion_linearSystem
  exact CompleteSystemBirationalIsomorphism.eventuallyBirational_of_nonzero_power_maps
    X.structureMorphism H A s hcover hclosed
    (NefTwistedMaps.eventually_nonzero_map_of_isCanonical X hregular K hK A H hA hpositive) j

end KltDP.Geometry.NefCompleteSystemBirationalIsomorphism
