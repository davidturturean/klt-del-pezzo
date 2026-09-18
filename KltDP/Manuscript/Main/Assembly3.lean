import KltDP.Manuscript.Main.Assembly2
import KltDP.Manuscript.S07.TwoContactRuling

/-!
# Theorem 1.1 modulo the terminal isolated-node exchange only

`uniformSevenPointBound_of_iso`: Theorem 1.1 with Theorems 7.1, 7.5 and 8.3 discharged; the only
remaining input is `IsolatedExchangeHyp` (Theorem 4.6 in its interface form), whose valency `≥ 2`
case is `S04.isolatedExchangeHyp_of_degree_ge_two` and whose terminal case is
`KltDP.Manuscript.S04.IsolatedNodeExchangeTerminal`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Theorem 1.1 modulo Theorem 4.6 (interface form). -/
theorem uniformSevenPointBound_of_iso (p : ℕ) [CharP k p] (hp : 2 < p)
    (hIso : ∀ R : ResolutionDatum k, R.IsMinimalCounterexample → IsolatedExchangeHyp R)
    (X : NormalProjectiveSurface k) (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1) :
    X.singularPoints.card ≤ 7 :=
  uniformSevenPointBound_of_hyps p hp
    (fun R hR P hP => S07.twoContactRulingHyp R p hp hR P hP) hIso X hDP hrank

end KltDP.Manuscript

#print axioms KltDP.Manuscript.uniformSevenPointBound_of_iso
