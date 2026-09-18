import KltDP.Manuscript.S07.AdjointConfiguration
import KltDP.Geometry.SevenPointHighCanonicalSquare

/-!
# The uniform seven-point bound: top-level assembly

Manuscript `source/manuscript.tex` lines 106–111 (Theorem 1.1, `thm:main`) and its proof at
lines 2844–2872: fix an algebraically closed field of characteristic `p > 2` and suppose a
counterexample exists; choose one whose minimal resolution has the least Picard number;
Theorem 7.1 produces the single exterior adjoint configuration and Theorem 8.3 excludes it.

`uniformSevenPointBound_of` is the assembly, stated with the two named inputs as explicit
hypotheses (`hAdjoint` = Theorem 7.1, `hExclusion` = Theorem 8.3), each quantified over all
data of a minimal counterexample. The unconditional theorem is obtained once both inputs
are proved; nothing here assumes them globally.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A counterexample: a rank-one klt del Pezzo surface with more than seven singular points. -/
def IsCounterexample (X : NormalProjectiveSurface k) : Prop :=
  IsKltDelPezzo X ∧ X.picardRank = 1 ∧ 7 < X.singularPoints.card

/-- A minimal counterexample: its minimal resolution has the least Picard number among the
minimal resolutions of all counterexamples over the same field. -/
def ResolutionDatum.IsMinimalCounterexample (R : ResolutionDatum k) : Prop :=
  7 < R.X.singularPoints.card ∧
    ∀ R' : ResolutionDatum k, 7 < R'.X.singularPoints.card → R.S.picardRank ≤ R'.S.picardRank

/-- Every counterexample admits a minimal counterexample datum (well-founded minimality of
`ρ(S)` over one fixed field, manuscript F33). -/
theorem exists_minimalCounterexample (X : NormalProjectiveSurface k) (hX : IsCounterexample X) :
    ∃ R : ResolutionDatum k, R.IsMinimalCounterexample := by
  obtain ⟨hDP, hrank, hcard⟩ := hX
  obtain ⟨S, π, hmin⟩ := GeneralResolution.exists_minimalResolution X
  let R₀ : ResolutionDatum k := ⟨S, X, π, hmin, hDP, hrank⟩
  have hne : ∃ n : ℕ, ∃ R : ResolutionDatum k, 7 < R.X.singularPoints.card ∧ R.S.picardRank = n :=
    ⟨R₀.S.picardRank, R₀, hcard, rfl⟩
  classical
  obtain ⟨R, hR, hRn⟩ := Nat.find_spec hne
  refine ⟨R, hR, fun R' hR' => ?_⟩
  rw [hRn]
  exact Nat.find_min' hne ⟨R', hR', rfl⟩

/-- **Theorem 1.1 (`thm:main`), assembled from Theorems 7.1 and 8.3.** -/
theorem uniformSevenPointBound_of
    (hAdjoint : ∀ R : ResolutionDatum k, R.IsMinimalCounterexample →
      ∃ P : R.S.PrimeCurve, R.IsShortestExteriorMinusOne P ∧ AdjointConfiguration R P)
    (hExclusion : ∀ (R : ResolutionDatum k) (P : R.S.PrimeCurve), R.IsMinimalCounterexample →
      R.IsShortestExteriorMinusOne P → AdjointConfiguration R P → False)
    (X : NormalProjectiveSurface k) (hDP : IsKltDelPezzo X) (hrank : X.picardRank = 1) :
    X.singularPoints.card ≤ 7 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨R, hR⟩ := exists_minimalCounterexample X ⟨hDP, hrank, hcon⟩
  obtain ⟨P, hP, hconf⟩ := hAdjoint R hR
  exact hExclusion R P hR hP hconf

/-- A minimal counterexample has `K_S² ≤ 1` and `ρ(S) ≥ 9` (manuscript lines 2848–2852, via
the compiled high-canonical-square bound). -/
theorem ResolutionDatum.IsMinimalCounterexample.canonicalSquare_le_one_and_picardRank
    (R : ResolutionDatum k) (hR : R.IsMinimalCounterexample) (p : ℕ) [CharP k p] (hp : 0 < p) :
    R.S.intersectionPairing R.hreg R.KS R.KS ≤ 1 ∧ 9 ≤ R.S.picardRank :=
  R.hmin.counterexample_canonical_square_and_picardRank R.hDP R.hrank p hp R.KS R.eKS hR.1

end KltDP.Manuscript
