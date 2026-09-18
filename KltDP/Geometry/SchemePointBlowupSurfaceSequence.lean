import KltDP.Geometry.SchemePointBlowupSequenceSmooth

/-!
The actual scheme-level point-blowup sequence is an accepted surface-level
sequence on its derived original source surface. Each original step, centre,
chart and comparison isomorphism is retained. The required field triangles
are the identities of the original composite structure morphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemePointBlowup

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]

/-- An original scheme point-blowup step is the same accepted surface
point blowup after equipping both original schemes with their derived properties. -/
theorem SequenceAway.step_isPointBlowupAt
    {S S' : Scheme.{u}} {U : Set X.toScheme} {g : S' ⟶ X.toScheme}
    (hg : SequenceAway X.toScheme U S' g)
    (b : S ⟶ S') (x : S') (hb : IsAt b x) (hx : g.base x ∉ U) :
    IsPointBlowupAt ((SequenceAway.step b g x hb hx hg).sourceSurface X)
      (hg.sourceSurface X) b x := by
  refine ⟨?_, hb⟩
  change b ≫ (g ≫ X.structureMorphism) = (b ≫ g) ≫ X.structureMorphism
  exact (Category.assoc b g X.structureMorphism).symm

/-- The same original finite sequence is an accepted point-blowup
sequence of the derived surfaces, with its exact original composite map. -/
theorem SequenceAway.toSurfaceSequence
    {S : Scheme.{u}} {U : Set X.toScheme} {f : S ⟶ X.toScheme}
    (h : SequenceAway X.toScheme U S f) :
    IsPointBlowupSequence (h.sourceSurface X) X f := by
  induction h with
  | of_isIso f hf =>
      exact IsPointBlowupSequence.of_isIso (k := k)
        (S := (SequenceAway.of_isIso (U := U) f hf).sourceSurface X)
        (T := X) f hf rfl
  | step b g x hb hx hg ih =>
      exact IsPointBlowupSequence.step (k := k)
        (S := (SequenceAway.step b g x hb hx hg).sourceSurface X)
        (S' := hg.sourceSurface X) (T := X) b g x
        (SequenceAway.step_isPointBlowupAt (k := k) X hg b x hb hx) ih

end KltDP.Geometry.SchemePointBlowup
