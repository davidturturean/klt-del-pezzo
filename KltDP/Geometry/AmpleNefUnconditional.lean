import KltDP.Geometry.GloballyGeneratedEffectiveCartier
import KltDP.Geometry.GloballyGeneratedNefReduction
import KltDP.Geometry.AmplePositivity

/-!
# Globally generated and semiample line bundles are nef; ample implies nef

At the generic point of each original prime curve, global generation supplies
an effective Cartier representative whose support misses that point.  The
accepted surface restriction-degree result then proves nonnegative degree on
the curve.  This discharges the explicit geometric input in `AmplePositivity`.

The resulting ample-implies-nef theorem has no `GloballyGeneratedSectionWitness`
or `GloballyGeneratedRestrictionNonneg` hypothesis.  It uses the existing
Serre ampleness definition and original sheaf-valued positivity predicates.
The project's four-entry literature allowlist is unchanged.  This module
introduces no new axiom and proves no ampleness witness or bigness claim.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AmpleNefUnconditional

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The formerly open section witness follows from a genuine section with
a unit coefficient at the original curve's generic point. -/
theorem globallyGeneratedSectionWitness : GloballyGeneratedNef.GloballyGeneratedSectionWitness X := by
  intro L hL C
  obtain ⟨E, hE, hx, ⟨e⟩⟩ :=
    GloballyGeneratedEffectiveCartier.exists_effectiveCartier_avoiding_point
      X.toScheme L hL C.genericPoint
  exact ⟨E, hE, hx, ⟨e⟩⟩

/-- A globally generated invertible sheaf has nonnegative degree on every
original prime curve, with the geometric witness fully discharged. -/
theorem globallyGeneratedRestrictionNonneg : AmplePositivity.GloballyGeneratedRestrictionNonneg X :=
  GloballyGeneratedNef.globallyGeneratedRestrictionNonneg_of_witness X
    (globallyGeneratedSectionWitness X)

/-- Semiample invertible sheaves are nef on the original surface. -/
theorem isNef_of_isSemiample (L : InvertibleSheaf X.toScheme)
    (hL : Positivity.IsSemiample L) : Positivity.IsNef X.structureMorphism L :=
  AmplePositivity.isNef_of_isSemiample X (globallyGeneratedRestrictionNonneg X) L hL

/-- Ampleness in the existing Serre definition implies nefness. -/
theorem isNef_of_isAmple (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) : Positivity.IsNef X.structureMorphism L :=
  AmplePositivity.isNef_of_isAmple X (globallyGeneratedRestrictionNonneg X) L hL

/-- The global-generation input is inhabited by the actual trivial
invertible sheaf, using the original free-singleton comparison. -/
theorem trivial_isGloballyGenerated (Y : Scheme.{u}) :
    Positivity.IsGloballyGenerated (InvertibleSheaf.trivial Y).obj := by
  exact ⟨PUnit, (_root_.SheafOfModules.freeUniqueIsoUnit (R := Y.ringCatSheaf) PUnit).hom,
    inferInstance⟩

end KltDP.Geometry.AmpleNefUnconditional
