import KltDP.Literature.StacksPointBlowupDomination
import KltDP.Geometry.ProperBirationalSurfaceDominationInput

/-!
# Point blowups dominating an original proper birational surface morphism

The full published literal is applied to the proved finite bad set of the
original map. Every geometric hypothesis is supplied by the compiled input
package. The resulting sequence avoids the original isomorphism open and
factors the given map; no comparison map is an additional assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProperBirationalSurface

/-- Domination by actual point blowups, with centres outside the original
maximal isomorphism open and with the original factorization retained. -/
theorem exists_pointBlowup_domination
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} [IsIntegral G]
    (T : NormalProjectiveSurface k) (f : G ⟶ T.toScheme) [IsProper f]
    (hbir : IsBirationalScheme f) (hreg : ∀ x, RegularPoint T.toScheme x) :
    ∃ (Z : Scheme.{u}) (b : Z ⟶ T.toScheme),
      SchemePointBlowup.SequenceAway T.toScheme
        (targetIsomorphismOpen f : Set T.toScheme) Z b ∧
      ∃ (g : Z ⟶ G), g ≫ f = b := by
  obtain ⟨B, hfinite, hclosed, hB, hNoetherian, hregular, hiso⟩ :=
    exists_domination_input_of_regular T f hbir hreg
  obtain ⟨Z, b, hb, g, hg⟩ :=
    KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal
      T.toScheme G f hNoetherian B hfinite hclosed
      (fun x hx => (hregular x hx).1) (fun x hx => (hregular x hx).2)
      inferInstance hiso
  refine ⟨Z, b, ?_, g, hg⟩
  simpa only [hB, targetNonisomorphismLocus, compl_compl] using hb

end KltDP.Geometry.ProperBirationalSurface

#check @KltDP.Geometry.ProperBirationalSurface.exists_pointBlowup_domination
#print axioms KltDP.Geometry.ProperBirationalSurface.exists_pointBlowup_domination
