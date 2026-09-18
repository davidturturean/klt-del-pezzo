import KltDP.Geometry.IsomorphismPicardUnimodular
import KltDP.Geometry.ResolutionContractionInduction

/-! Actual regular-target resolution induction preserves the original integral
Picard unimodularity test in both directions. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

/-- The original integral Picard pairing is unimodular on an actual
resolution exactly when it is on its original regular target. -/
theorem IsResolution.picardUnimodular_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hres : IsResolution S X π)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x) :
    S.PicardUnimodular hres.regular ↔ X.PicardUnimodular hX := by
  let P : NormalProjectiveSurface k → Prop := fun T =>
    ∀ hT : ∀ t : T.Point, RegularPoint T.toScheme t,
      T.PicardUnimodular hT ↔ X.PicardUnimodular hX
  have h : P S := by
    apply hres.regular_target_induction hX P
    · intro T g hg hgk hT
      letI : IsIso g := hg
      exact picardUnimodular_iff_of_isIso g hgk hT hX
    · intro T T' hT E b hminus hb ih hT0
      exact (hb.picardUnimodular_iff hT hminus).trans (ih hb.regular)
  exact h hres.regular

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.picardUnimodular_iff
#print axioms KltDP.Geometry.IsResolution.picardUnimodular_iff
