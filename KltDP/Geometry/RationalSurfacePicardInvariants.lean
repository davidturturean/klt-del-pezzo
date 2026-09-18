import KltDP.Geometry.BirationalOverPicardUnimodular
import KltDP.Geometry.PicardUnimodularTorsionFree
import KltDP.Geometry.RationalSurfaceNoetherRelation

/-! The three original rational-surface invariants follow from the actual
birational correspondence to the affine plane and original surface geometry. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open KltDP.Examples.FrobeniusStageZeroProjective

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (hrational : Scheme.BirationalOver S.structureMorphism
    (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)))

include hrational in
/-- Unimodularity of the actual integral Picard pairing on the rational surface. -/
theorem picardUnimodular_of_birationalOver_affinePlane : S.PicardUnimodular hS := by
  have hST : Scheme.BirationalOver S.structureMorphism
      (projectiveProductSurface (k := k)).structureMorphism :=
    hrational.trans KltDP.Examples.ProjectiveLineProductRationality.birationalOver_affinePlane.symm
  exact (picardUnimodular_iff_of_birationalOver S projectiveProductSurface hS
    KltDP.Examples.FrobeniusRulingClassPairing.baseRegular hST).mpr
      KltDP.Examples.ProjectiveLineProductLattice.picardUnimodular

include hS hrational in
/-- All three assertions concern the original Picard group, original numerical
quotient and supplied actual canonical Cartier divisor. -/
theorem rational_surface_invariants
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2) :
    S.PicardUnimodular hS ∧ S.PicardTorsionFree ∧ S.NoetherRelationFor hS K := by
  have hU := S.picardUnimodular_of_birationalOver_affinePlane hS hrational
  exact ⟨hU, S.picardTorsionFree_of_picardUnimodular hS hU,
    S.noetherRelation_of_birationalOver_affinePlane hS hrational K eK⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.rational_surface_invariants
#print axioms KltDP.Geometry.NormalProjectiveSurface.rational_surface_invariants
