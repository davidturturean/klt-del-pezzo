import KltDP.Geometry.ResolutionMinimalFactorization
import KltDP.Geometry.MinimalResolutionRegularTarget
import KltDP.Geometry.SurfacePointBlowupSequenceGeometry

/-!
# Point-blowup factorization of the original regular-target resolution

Minimalization constructs the actual point-blowup sequence and original
factor map. The minimal factor over the regular target is an isomorphism,
so it is absorbed into the last isomorphism of that same sequence.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k]

/-- Append an original isomorphism over the field to the actual sequence. -/
theorem IsPointBlowupSequence.comp_isIso
    {S T X : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
    (hb : IsPointBlowupSequence S T b) (g : T.toScheme ⟶ X.toScheme)
    (hg : IsIso g) (hgk : g ≫ X.structureMorphism = T.structureMorphism) :
    IsPointBlowupSequence S X (b ≫ g) := by
  induction hb with
  | of_isIso b hb hbk =>
      letI : IsIso b := hb
      letI : IsIso g := hg
      exact IsPointBlowupSequence.of_isIso (b ≫ g) (by infer_instance)
        (by rw [Category.assoc, hgk, hbk])
  | step b c x hb hc ih =>
      simpa only [Category.assoc] using
        IsPointBlowupSequence.step b (c ≫ g) x hb (ih g hg hgk)

/-- A resolution of an everywhere regular original target is a sequence of
point blowups, with no independently supplied factorization. -/
theorem IsResolution.isPointBlowupSequence_of_target_regular [IsAlgClosed k]
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hres : IsResolution S X π)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x) :
    IsPointBlowupSequence S X π := by
  obtain ⟨T, b, g, hb, hg, hfac⟩ := hres.exists_minimalFactorization
  rw [← hfac]
  exact hb.comp_isIso g (hg.isIso_of_target_regular hX) hg.over_base

/-- The original proper birational morphism of smooth projective surfaces
has an actual point-blowup factorization. -/
theorem isPointBlowupSequence_of_smooth_birational [IsAlgClosed k]
    (S X : NormalProjectiveSurface k)
    [IsSmooth S.structureMorphism] [IsSmooth X.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hbir : IsBirationalScheme π) : IsPointBlowupSequence S X π := by
  have hres : IsResolution S X π :=
    ⟨hπ, S.regularPoints_of_isSmooth, (isBirational_iff_isBirationalScheme π).mpr hbir⟩
  exact hres.isPointBlowupSequence_of_target_regular X.regularPoints_of_isSmooth

end KltDP.Geometry

#check @KltDP.Geometry.isPointBlowupSequence_of_smooth_birational
#print axioms KltDP.Geometry.isPointBlowupSequence_of_smooth_birational
