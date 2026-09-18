import KltDP.Geometry.ContractionPicardUnimodular
import KltDP.LinearAlgebra.IsometryIntegralDual

/-! The original Picard pullback equivalence and original intersection
projection formula preserve the original integral-dual unimodularity test. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- The original integral Picard pairing is unimodular on one of two
isomorphic surfaces over the field exactly when it is on the other. -/
theorem picardUnimodular_iff_of_isIso
    {k : Type u} [Field k] [IsAlgClosed k]
    {S T : NormalProjectiveSurface k} (f : S.toScheme ⟶ T.toScheme) [IsIso f]
    (hf : f ≫ T.structureMorphism = S.structureMorphism)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t) :
    S.PicardUnimodular hS ↔ T.PicardUnimodular hT := by
  have hbir : IsBirationalScheme f :=
    ⟨genericPoint_eq_of_isOpenImmersion f, inferInstance⟩
  rw [S.picardUnimodular_iff_bilinForm hS, T.picardUnimodular_iff_bilinForm hT]
  apply KltDP.LinearAlgebra.dual_bijective_iff_of_isometry
    (T.integralPicardIntersectionBilinForm hT) (S.integralPicardIntersectionBilinForm hS)
    (PointBlowupPicard.pullbackEquivOfIso (asIso f)).toAdditive
  intro a b
  rw [S.integralPicardIntersectionBilinForm_apply, T.integralPicardIntersectionBilinForm_apply]
  exact BirationalPicardIntersectionPullback.picardPairing_pullback f hf hbir hS hT a.toMul b.toMul

end KltDP.Geometry

#check @KltDP.Geometry.picardUnimodular_iff_of_isIso
#print axioms KltDP.Geometry.picardUnimodular_iff_of_isIso
