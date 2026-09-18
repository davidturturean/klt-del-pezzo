import KltDP.Geometry.AbsoluteMinimalSurface
import KltDP.Geometry.MinimalResolutionRegularTarget

/-! # The original absolute minimal target has no nontrivial smooth blowdown -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Global absence of minus-one curves gives the ordinary birational
morphism formulation of relative minimality, on the same original maps. -/
theorem isIso_of_no_minusOneCurve
    (V : NormalProjectiveSurface k)
    (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
    (hmin : ∀ C : V.PrimeCurve, ¬ IsMinusOneCurve hV C)
    (T : NormalProjectiveSurface k)
    (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
    (b : V.toScheme ⟶ T.toScheme)
    (hover : b ≫ T.structureMorphism = V.structureMorphism)
    (hbir : IsBirational b) : IsIso b := by
  have hres : IsMinimalResolution V T b :=
    { toIsResolution := ⟨hover, hV, hbir⟩
      no_minusOne_curve := fun C _ => hmin C }
  exact hres.isIso_of_target_regular hT

/-- The constructed original target satisfies the literal birational
morphism formulation as well as the actual no-minus-one condition. -/
theorem exists_absoluteMinimalModel_birationalIso (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) :
    ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
      (b : S.toScheme ⟶ V.toScheme),
      IsPointBlowupSequence S V b ∧
      (∀ C : V.PrimeCurve, ¬ IsMinusOneCurve hV C) ∧
      b ≫ V.structureMorphism = S.structureMorphism ∧
      ∀ (T : NormalProjectiveSurface k)
        (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
        (g : V.toScheme ⟶ T.toScheme),
        g ≫ T.structureMorphism = V.structureMorphism → IsBirational g → IsIso g := by
  obtain ⟨V, hV, b, hseq, hmin, hover, _⟩ := S.exists_absoluteMinimalModel hS
  exact ⟨V, hV, b, hseq, hmin, hover, V.isIso_of_no_minusOneCurve hV hmin⟩

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.isIso_of_no_minusOneCurve
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_absoluteMinimalModel_birationalIso
