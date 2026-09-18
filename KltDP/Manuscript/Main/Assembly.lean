import KltDP.Manuscript.Main.SevenPointBound
import KltDP.Manuscript.S08.ForestExclusion

/-!
# Assembly of Theorem 1.1 with Theorem 8.3 discharged

`uniformSevenPointBound_of_adjoint`: Theorem 1.1 (`thm:main`) with the forest exclusion
(Theorem 8.3, `KltDP.Manuscript.S08.singleAdjointForestImpossible`) discharged; only the
adjoint reduction (Theorem 7.1) remains as an explicit hypothesis.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Theorem 1.1 with Theorem 8.3 discharged.** -/
theorem uniformSevenPointBound_of_adjoint (p : ℕ) [CharP k p] (hp : 2 < p)
    (hAdjoint : ∀ R : ResolutionDatum k, R.IsMinimalCounterexample →
      ∃ P : R.S.PrimeCurve, R.IsShortestExteriorMinusOne P ∧ AdjointConfiguration R P)
    (X : NormalProjectiveSurface k) (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1) :
    X.singularPoints.card ≤ 7 :=
  uniformSevenPointBound_of hAdjoint
    (fun R P hR hP hconf => S08.singleAdjointForestImpossible R P p hp hR hP hconf) X hDP hrank

end KltDP.Manuscript

#print axioms KltDP.Manuscript.uniformSevenPointBound_of_adjoint
