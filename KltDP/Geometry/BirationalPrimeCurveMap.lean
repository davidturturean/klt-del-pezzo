import KltDP.Geometry.BirationalPrimeCorrespondence
import KltDP.Geometry.GluedIdealSheafLift
import KltDP.Geometry.SchematicImageDenseOpen
import KltDP.Geometry.PrimeCurveGenericStalkParameter

/-!
# The original morphism between corresponding prime curves

The actual source prime has the original target prime as its whole image.
Reducedness therefore identifies the original composite's kernel with the
target prime's vanishing ideal. The existing quotient-gluing lift constructs
the restriction map, with its literal inclusion and ground-field squares.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.BirationalPrimeCurveMap

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
  (C : X.PrimeCurve)

theorem composite_range :
    Set.range (((abovePrimeCurve π hbir C).inclusion ≫ π).base) =
      (C : Set X.toScheme) := by
  change Set.range (π.base ∘ (abovePrimeCurve π hbir C).inclusion.base) = _
  rw [Set.range_comp, NormalProjectiveSurface.PrimeCurve.range_inclusion,
    abovePrimeCurve_image]

theorem composite_kernel_support :
    ((abovePrimeCurve π hbir C).inclusion ≫ π).ker.support = C.closedSubset := by
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.Hom.support_ker, composite_range, C.isClosed.closure_eq]
  rfl

theorem composite_kernel :
    ((abovePrimeCurve π hbir C).inclusion ≫ π).ker = C.vanishingIdeal := by
  rw [← SchematicImageDenseOpen.ker_radical
      ((abovePrimeCurve π hbir C).inclusion ≫ π),
    ← Scheme.IdealSheafData.vanishingIdeal_support, composite_kernel_support]
  rfl

/-- The restriction of the original surface morphism to its actual prime above C. -/
def restriction : (abovePrimeCurve π hbir C).toScheme ⟶ C.toScheme :=
  GluedIdealSheafLift.liftGlued C.vanishingIdeal
    ((abovePrimeCurve π hbir C).inclusion ≫ π) (composite_kernel π hbir C).ge

@[reassoc]
theorem restriction_inclusion :
    restriction π hbir C ≫ C.inclusion = (abovePrimeCurve π hbir C).inclusion ≫ π :=
  GluedIdealSheafLift.liftGlued_gluedTo _ _ _

instance restriction_isProper : IsProper (restriction π hbir C) := by
  letI : IsProper (restriction π hbir C ≫ C.inclusion) := by
    rw [restriction_inclusion]
    infer_instance
  exact IsProper.of_comp_of_isSeparated (restriction π hbir C) C.inclusion

theorem restriction_toSpec (hπ : π ≫ X.structureMorphism = S.structureMorphism) :
    restriction π hbir C ≫ C.toSpec = (abovePrimeCurve π hbir C).toSpec := by
  change restriction π hbir C ≫ (C.inclusion ≫ X.structureMorphism) =
    (abovePrimeCurve π hbir C).inclusion ≫ S.structureMorphism
  rw [← Category.assoc, restriction_inclusion, Category.assoc, hπ]

theorem restriction_map_genericPoint :
    (restriction π hbir C).base (_root_.genericPoint (abovePrimeCurve π hbir C).toScheme) =
      _root_.genericPoint C.toScheme := by
  apply C.inclusion.isClosedEmbedding.injective
  calc
    C.inclusion.base ((restriction π hbir C).base
        (_root_.genericPoint (abovePrimeCurve π hbir C).toScheme)) =
      π.base ((abovePrimeCurve π hbir C).inclusion.base
        (_root_.genericPoint (abovePrimeCurve π hbir C).toScheme)) := by
          simpa only [Scheme.comp_base_apply] using congrArg
            (fun f => f.base (_root_.genericPoint (abovePrimeCurve π hbir C).toScheme))
            (restriction_inclusion π hbir C)
    _ = C.inclusion.base (_root_.genericPoint C.toScheme) := by
      rw [NormalProjectiveSurface.PrimeCurve.inclusion_genericPoint_eq,
        abovePrimeCurve_map_genericPoint,
        NormalProjectiveSurface.PrimeCurve.inclusion_genericPoint_eq]

instance restriction_genericPointPreserving : GenericPointPreserving (restriction π hbir C) :=
  ⟨restriction_map_genericPoint π hbir C⟩

end KltDP.Geometry.BirationalPrimeCurveMap

#check @KltDP.Geometry.BirationalPrimeCurveMap.restriction
#check @KltDP.Geometry.BirationalPrimeCurveMap.restriction_toSpec
#print axioms KltDP.Geometry.BirationalPrimeCurveMap.restriction_inclusion
#print axioms KltDP.Geometry.BirationalPrimeCurveMap.restriction_map_genericPoint
