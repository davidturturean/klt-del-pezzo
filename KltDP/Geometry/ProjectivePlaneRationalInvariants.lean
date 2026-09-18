import KltDP.Geometry.ProjectiveSpaceAffineRationality
import KltDP.Geometry.RationalSurfacePicardInvariants

/-! The projective-plane rationality conclusion supplies the existing
invariants of the same original surface and canonical Cartier divisor. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (hrational : Scheme.BirationalOver S.structureMorphism (projectiveSpaceToSpec k 2))

include hrational in
/-- The original projective-plane rationality witness gives unimodularity. -/
theorem picardUnimodular_of_birationalOver_projectivePlane : S.PicardUnimodular hS :=
  S.picardUnimodular_of_birationalOver_affinePlane hS
    ((ProjectiveChart.birationalOver_projectiveSpace_iff k 2 S.structureMorphism).mp hrational)

include hS hrational in
/-- All three invariants retain the original Picard group, numerical
quotient, and actual supplied canonical divisor and sheaf identification. -/
theorem rational_surface_invariants_of_birationalOver_projectivePlane
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2) :
    S.PicardUnimodular hS ∧ S.PicardTorsionFree ∧ S.NoetherRelationFor hS K :=
  S.rational_surface_invariants hS
    ((ProjectiveChart.birationalOver_projectiveSpace_iff k 2 S.structureMorphism).mp hrational)
    K eK

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.rational_surface_invariants_of_birationalOver_projectivePlane
#print axioms KltDP.Geometry.NormalProjectiveSurface.rational_surface_invariants_of_birationalOver_projectivePlane
