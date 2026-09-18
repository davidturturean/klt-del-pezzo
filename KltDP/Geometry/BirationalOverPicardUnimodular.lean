import KltDP.Geometry.RegularResolutionPicardUnimodular
import KltDP.Geometry.CommonResolutionFromBirationalOver

/-! The original dense-open isomorphism constructs both actual resolutions,
so unimodularity of the original integral Picard forms is birationally invariant. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- The original integral Picard pairing is unimodular on either of two
regular surfaces with an actual birational correspondence over the field. -/
theorem picardUnimodular_iff_of_birationalOver
    {k : Type u} [Field k] [IsAlgClosed k]
    (S T : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
    (h : Scheme.BirationalOver S.structureMorphism T.structureMorphism) :
    S.PicardUnimodular hS ↔ T.PicardUnimodular hT := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hS
  letI : IsSmooth S.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism
  obtain ⟨Z, b, q, hb, hq, _, _⟩ := exists_common_resolution_of_birationalOver S T h
  exact (hb.picardUnimodular_iff hS).symm.trans (hq.picardUnimodular_iff hT)

end KltDP.Geometry

#check @KltDP.Geometry.picardUnimodular_iff_of_birationalOver
#print axioms KltDP.Geometry.picardUnimodular_iff_of_birationalOver
