import KltDP.Geometry.KeelExceptionalSupportComparison
import KltDP.Geometry.CurveKeelBirationalIff
import KltDP.Geometry.NefCompleteSystemBirationalIsomorphism
import KltDP.Geometry.NefPositiveSelfIntersectionBig
import KltDP.Geometry.BignessIsomorphism
import KltDP.Geometry.SurfaceIrreducibleClosedDimension

/-!
# The two actual exceptional loci on a nef positive-square surface

Every positive-dimensional original reduced subvariety is a curve or the
whole surface. On curves, the proved degree comparison identifies eventual
complete-system birationality with original section-growth bigness. The
whole-surface inclusion is an actual isomorphism: the original embedding
and power maps pull back to it, and original bigness pulls back as well.
This proves the pointwise comparison needed for the actual exceptional
supports, without an all-dimensional growth/birationality assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.KeelSurfaceExceptionalComparison

attribute [local instance] KeelCompleteSystem.subvariety_isIntegral

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    (K : X.WeilDivisor) (hK : SurfaceRiemannRochSource.IsCanonical X hregular K)
    (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection hregular L)

local instance original_proper : IsProper X.structureMorphism := X.projective.isProper

include hregular K hK hnef hpositive

/-- The actual restricted line has eventual birational complete systems
exactly when it has the unchanged growth bigness on each original subvariety. -/
theorem restriction_eventuallyBirational_iff_isBig
    (Z : IrreducibleCloseds X.toScheme)
    (hZ : 0 < topologicalKrullDim (Z : Set X.toScheme)) :
    KeelCompleteSystem.EventuallyBirational (Positivity.inclusion Z ≫ X.structureMorphism)
        (pullbackInvertibleSheaf (Positivity.inclusion Z) L) ↔
      Positivity.IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
        (pullbackInvertibleSheaf (Positivity.inclusion Z) L) := by
  rcases X.irreducibleClosed_dim_eq_one_or_eq_univ Z hZ with hcurve | hwhole
  · exact CurveKeelBirational.eventuallyBirational_iff_isBig_of_nonneg
      (Positivity.inclusion Z ≫ X.structureMorphism)
      (KeelCompleteSystem.subvariety_isProjective X.structureMorphism X.projective Z)
      ((ZeroDimensionalSubvarietyBigness.toScheme_dimension Z).trans hcurve)
      (pullbackInvertibleSheaf (Positivity.inclusion Z) L) (hnef Z hcurve)
  · letI : Surjective (Positivity.inclusion Z) :=
      ⟨Set.range_eq_univ.mp ((Positivity.range_inclusion Z).trans hwhole)⟩
    letI : IsIso (Positivity.inclusion Z) :=
      isIso_of_isClosedImmersion_of_surjective (Positivity.inclusion Z)
    have hbir :=
      NefCompleteSystemBirationalIsomorphism.eventuallyBirational_pullback_of_isCanonical
        X hregular K hK L hnef hpositive (Positivity.inclusion Z)
    have hbig := (BignessIsomorphism.isBig_pullback_iff
      (Positivity.inclusion Z) X.structureMorphism L).mpr
        (NefPositiveSelfIntersectionBig.isBig_of_isCanonical
          X hregular K hK L hnef hpositive)
    exact ⟨fun _ => hbig, fun _ => hbir⟩

/-- The complete-system exceptional support is the original growth-defined null locus. -/
theorem exceptionalSupport_eq_nullLocus :
    KeelCompleteSystem.exceptionalSupport X.structureMorphism L =
      Positivity.nullLocus X.structureMorphism L :=
  KeelCompleteSystem.exceptionalSupport_eq_nullLocus_of_birational_iff_big
    X.structureMorphism L
      (restriction_eventuallyBirational_iff_isBig X hregular K hK L hnef hpositive)

/-- The canonical comparison is between the actual reduced exceptional schemes. -/
def exceptionalSchemeIso :
    KeelCompleteSystem.exceptionalScheme X.structureMorphism L ≅
      Positivity.nullLocusScheme X.structureMorphism L :=
  KeelCompleteSystem.exceptionalSchemeIso X.structureMorphism L
    (exceptionalSupport_eq_nullLocus X hregular K hK L hnef hpositive)

end KltDP.Geometry.KeelSurfaceExceptionalComparison
