import KltDP.Manuscript.Main.Assembly
import KltDP.Manuscript.S07.AdjointReduction

/-!
# Theorem 1.1 with Theorem 7.1 discharged, modulo the two interface facts

`uniformSevenPointBound_of_hyps`: Theorem 1.1 assuming only `TwoContactRulingHyp` (Theorem 7.5, for
shortest exterior `(-1)`-curves of minimal counterexamples) and `IsolatedExchangeHyp` (Theorem 4.6).
Both are being discharged in `KltDP.Manuscript.S07.TwoContactRuling` and
`KltDP.Manuscript.S04.IsolatedNodeExchangeTerminal`; the unconditional theorem is
`KltDP.Manuscript.uniformSevenPointBound` in `Main/Final.lean`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Theorem 1.1 modulo Theorems 7.5 and 4.6 (interface forms). -/
theorem uniformSevenPointBound_of_hyps (p : ℕ) [CharP k p] (hp : 2 < p)
    (hTwo : ∀ R : ResolutionDatum k, R.IsMinimalCounterexample →
      ∀ P, R.IsShortestExteriorMinusOne P → TwoContactRulingHyp R P)
    (hIso : ∀ R : ResolutionDatum k, R.IsMinimalCounterexample → IsolatedExchangeHyp R)
    (X : NormalProjectiveSurface k) (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1) :
    X.singularPoints.card ≤ 7 :=
  uniformSevenPointBound_of_adjoint p hp
    (fun R hR => S07.singleExteriorAdjointReduction_of R p hp hR (hTwo R hR) (hIso R hR)) X hDP hrank

end KltDP.Manuscript

#print axioms KltDP.Manuscript.uniformSevenPointBound_of_hyps
