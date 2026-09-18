import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Geometry.PrimeCurveInclusionLift

/-!
# The actual closed image of an original prime-curve scheme

An original prime curve already has scheme dimension one. Its closed
image has the same dimension by the original embedding homeomorphism,
so it is an actual prime curve on the target surface. The accepted
prime-curve inclusion lift identifies its reduced curve scheme with the
original source and retains the original closed immersion.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

variable {k : Type u} [Field k] {S T : NormalProjectiveSurface k}
    (C : S.PrimeCurve) (f : C.toScheme ⟶ T.toScheme) [IsClosedImmersion f]

/-- The image of the original curve's actual closed immersion is an actual target prime curve. -/
def closedImage : T.PrimeCurve :=
  ⟨⟨Set.range f.base, PrimeCurveOfClosedImmersion.range_isIrreducible T f,
      f.isClosedEmbedding.isClosed_range⟩,
    (IsHomeomorph.topologicalKrullDim_eq _
      f.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm.trans
      C.dimension_one_toScheme⟩

@[simp]
theorem coe_closedImage : (C.closedImage f : Set T.toScheme) = Set.range f.base := rfl

/-- The actual closed image curve scheme is isomorphic to its original curve source. -/
def closedImageSourceIso : (C.closedImage f).toScheme ≅ C.toScheme :=
  (asIso (PrimeCurveInclusionLift.lift (C.closedImage f) f rfl)).symm

@[reassoc]
theorem closedImageSourceIso_hom_map :
    (C.closedImageSourceIso f).hom ≫ f = (C.closedImage f).inclusion :=
  (PrimeCurveInclusionLift.inclusion_eq_inv_lift (C.closedImage f) f rfl).symm

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

#print axioms KltDP.Geometry.NormalProjectiveSurface.PrimeCurve.closedImage
#print axioms KltDP.Geometry.NormalProjectiveSurface.PrimeCurve.closedImageSourceIso_hom_map
