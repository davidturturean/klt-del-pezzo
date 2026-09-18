import KltDP.Geometry.KeelCompleteSystemBirational
import KltDP.Geometry.ZeroDimensionalSubvarietyBigness
import KltDP.Geometry.ProjectiveProper

/-!
Keel's exceptional support using the actual eventual complete-system
predicate on each original reduced irreducible subvariety. The ambient
scheme need not be integral, normal, reduced, smooth, or geometrically
integral. The reduced scheme and restricted line use the existing
vanishing-ideal gluing and original pullback functor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.KeelCompleteSystem

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Projectivity restricts to the original reduced closed subvariety. -/
theorem subvariety_isProjective (hproj : IsProjectiveOverField f)
    (Z : IrreducibleCloseds X) :
    IsProjectiveOverField (Positivity.inclusion Z ≫ f) := by
  obtain ⟨n, i, hi, hfactor⟩ := hproj
  letI : IsClosedImmersion i := hi
  refine ⟨n, Positivity.inclusion Z ≫ i, inferInstance, ?_⟩
  rw [Category.assoc, hfactor]

local instance subvariety_isIntegral (Z : IrreducibleCloseds X) :
    IsIntegral (Positivity.toScheme Z) :=
  ZeroDimensionalSubvarietyBigness.toScheme_isIntegral Z

variable [IsProper f]

/-- The original subvariety structure morphism inherits properness. -/
theorem subvariety_isProper (Z : IrreducibleCloseds X) :
    IsProper (Positivity.inclusion Z ≫ f) := inferInstance

/-- A positive-dimensional original irreducible subvariety whose restricted
line does not have eventually birational complete systems. -/
def IsExceptionalSubvariety (L : InvertibleSheaf X) (Z : IrreducibleCloseds X) : Prop :=
  0 < topologicalKrullDim (Z : Set X) ∧
    ¬ EventuallyBirational (Positivity.inclusion Z ≫ f)
      (pullbackInvertibleSheaf (Positivity.inclusion Z) L)

/-- The closure of the union of those original subvarieties. -/
def exceptionalSupport (L : InvertibleSheaf X) : Set X :=
  closure (⋃ Z ∈ {Z : IrreducibleCloseds X | IsExceptionalSubvariety f L Z}, (Z : Set X))

theorem exceptionalSupport_isClosed (L : InvertibleSheaf X) :
    IsClosed (exceptionalSupport f L) := isClosed_closure

theorem subset_exceptionalSupport (L : InvertibleSheaf X)
    {Z : IrreducibleCloseds X} (hZ : IsExceptionalSubvariety f L Z) :
    (Z : Set X) ⊆ exceptionalSupport f L :=
  (Set.subset_biUnion_of_mem (u := fun Z : IrreducibleCloseds X => (Z : Set X)) hZ).trans
    subset_closure

def exceptionalClosed (L : InvertibleSheaf X) : Closeds X :=
  ⟨exceptionalSupport f L, exceptionalSupport_isClosed f L⟩

/-- The actual reduced induced closed subscheme on the exceptional support. -/
def exceptionalScheme (L : InvertibleSheaf X) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (exceptionalClosed f L)).glueData.glued

/-- Its original closed immersion into the ambient scheme. -/
def exceptionalInclusion (L : InvertibleSheaf X) : exceptionalScheme f L ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal (exceptionalClosed f L)).gluedTo

instance exceptionalInclusion_isClosedImmersion (L : InvertibleSheaf X) :
    IsClosedImmersion (exceptionalInclusion f L) :=
  (Scheme.IdealSheafData.vanishingIdeal (exceptionalClosed f L)).gluedTo_isClosedImmersion

theorem range_exceptionalInclusion (L : InvertibleSheaf X) :
    Set.range (exceptionalInclusion f L).base = exceptionalSupport f L :=
  (Scheme.IdealSheafData.vanishingIdeal (exceptionalClosed f L)).range_gluedTo

instance exceptionalScheme_isReduced (L : InvertibleSheaf X) :
    IsReduced (exceptionalScheme f L) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (exceptionalClosed f L)
  exact I.glued_isReduced (Scheme.IdealSheafData.vanishingIdeal_support (I := I)).symm

/-- The original reduced exceptional scheme has the original support's topology. -/
def exceptionalSupportHomeomorph (L : InvertibleSheaf X) :
    exceptionalScheme f L ≃ₜ exceptionalSupport f L :=
  (Scheme.IdealSheafData.vanishingIdeal (exceptionalClosed f L)).gluedSupportHomeomorph

/-- The actual restricted line bundle on the whole reduced exceptional scheme. -/
def exceptionalRestrict (L : InvertibleSheaf X) : InvertibleSheaf (exceptionalScheme f L) :=
  pullbackInvertibleSheaf (exceptionalInclusion f L) L

instance exceptionalStructure_isProper (L : InvertibleSheaf X) :
    IsProper (exceptionalInclusion f L ≫ f) := inferInstance

/-- The original reduced exceptional scheme is projective over the original field. -/
theorem exceptionalStructure_isProjective (hproj : IsProjectiveOverField f)
    (L : InvertibleSheaf X) :
    IsProjectiveOverField (exceptionalInclusion f L ≫ f) := by
  obtain ⟨n, i, hi, hfactor⟩ := hproj
  letI : IsClosedImmersion i := hi
  refine ⟨n, exceptionalInclusion f L ≫ i, inferInstance, ?_⟩
  rw [Category.assoc, hfactor]

end KltDP.Geometry.KeelCompleteSystem
