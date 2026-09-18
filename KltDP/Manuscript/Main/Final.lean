import KltDP.Manuscript.Main.Assembly3
import KltDP.Manuscript.S04.IsolatedNodeExchangeTerminal
import KltDP.Literature.Stacks.BlowupRegularPointAdmitted
import KltDP.Literature.Hartshorne.StrictTransformInstance

/-!
# Theorem 1.1 (`thm:main`), unconditional

`uniformSevenPointBound`: over an algebraically closed field of characteristic `p > 2`, a klt del
Pezzo surface of Picard number one has at most seven singular points.

Proof structure (manuscript lines 2844–2872): minimal counterexample (`exists_minimalCounterexample`),
Theorem 7.1 (`S07.singleExteriorAdjointReduction_of`, with Theorem 7.5
`S07.twoContactRulingHyp` and Theorem 4.6 `S04.isolatedExchangeHyp_of_literal`), Theorem 8.3
(`S08.singleAdjointForestImpossible`).

Axioms beyond the union's accepted literature literals: `Tanaka.contraction_44_instance`
(Theorem 4.4 of Tanaka 2018), `Hartshorne.hurwitz_degreeTwo_projectiveLine_instance`
(Hurwitz, degree two), `Stacks.blowupRegularPoint_literal` (point blowup),
`Hartshorne.hasContractionLifts_instance` (strict transforms).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Theorem 4.6 in the interface form, all valencies. -/
theorem isolatedExchangeHyp_all (R : ResolutionDatum k) (p : ℕ) [CharP k p] (hp : 0 < p) :
    IsolatedExchangeHyp R := by
  classical
  exact S04.isolatedExchangeHyp_of_literal (KltDP.Literature.Stacks.blowupRegularPoint_literal k)
    (KltDP.Literature.Hartshorne.hasContractionLifts_instance k) R p hp

/-- **Theorem 1.1 (`thm:main`).** Over an algebraically closed field of characteristic `p > 2`,
every klt del Pezzo surface of Picard number one has at most seven singular points. -/
theorem uniformSevenPointBound (p : ℕ) [CharP k p] (hp : 2 < p)
    (X : NormalProjectiveSurface k) (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1) :
    X.singularPoints.card ≤ 7 :=
  uniformSevenPointBound_of_iso p hp (fun R _hR => isolatedExchangeHyp_all R p (by omega)) X hDP hrank

end KltDP.Manuscript

#print axioms KltDP.Manuscript.uniformSevenPointBound
