import KltDP.Manuscript.S07.Interfaces
import KltDP.Manuscript.S07.BisectionAdjoint
import KltDP.Manuscript.S07.BisectionRamification
import KltDP.Manuscript.S07.HurwitzInput
import KltDP.Manuscript.S06.SquareOneBound
import KltDP.Manuscript.S06.ThreeContactDescent
import KltDP.Manuscript.S04.OneComponentReplacement
import KltDP.Manuscript.S04.IsolatedNodeExchange
import KltDP.Manuscript.S04.DiscrepancyLemmas
import KltDP.Geometry.KltResolutionNoetherRelation

/-!
# Manuscript Theorem 7.5: the two-contact ruling

Source: `source/manuscript.tex`, lines 2236–2316, `thm:two-contact-ruling`.

Setting: a minimal counterexample `R` (`R.IsMinimalCounterexample`) in characteristic `p > 2`, a
shortest exterior `(-1)`-curve `P`, and two distinct non-adjacent weight-two exceptional curves
`U, V` meeting `P` once each. The Cartier divisor `F = U + 2P + V` (`ResolutionDatum.fibreDivisor`)
is nef with `F² = 0` and `K_S · F = -2` (section `FibreDivisor`), so Lemma 3.1
(`primitiveSquareZero_ruling`) gives the rational ruling `g : S → P¹`, and `L · F = 2ℓ`, so the
fibre-degree equalities of Lemma 7.3 apply.

* `count_le_seven_of_sections` (all-section case, TeX 2258–2278): every section meets a retained
  component of each pattern-`(2)` fibre (`a_t ≥ s`, `r_t ≤ 2`), the retained part of a
  pattern-`(1, 1)` fibre is a connected chain (`r_t ≤ 1`), there are at most `s − 1` fibres of
  pattern `(1, 1)` (Lemma 7.3), the distinguished fibre `U + 2P + V` has pattern `(2)`
  (`inFiber_distinguished`: its components are exactly `U, V, P`), each section meets `U` or `V`
  (so `s ≤ 6` by Lemma 4.4), and Lemma 7.1 (`forestCount`) gives `#π₀(D) ≤ s + 1 ≤ 7` for `s ≥ 2`
  and `#π₀(D) ≤ 4` for `s = 1` (at most three reducible fibres, one per edge at the section).
* `singularPoints_le_seven_of_bisection` (bisection case, TeX 2280–2316) with the adjoint
  `N ∼ K_S + F + H` of Lemma 7.4: if `H` is the only horizontal vertex, the retained curves away
  from the fibre of `N` are disjoint from `H`, so those fibres are branch points of the tame
  degree-two map `H → P¹` and there are at most two of them (Lemma 7.2 with the Hurwitz instance),
  giving `#π₀(D) ≤ 6`; if another horizontal vertex exists then `N = R'` with `μ_{R'} = 1`, and
  either `H² = -2` (`K_S² = 1`, eight exceptional curves by Noether, so an edge gives `≤ 7`
  and the edge-free case contradicts Theorem 6.7), or `H² ≤ -3` and the fibre of `R'` is a chain
  `Q − C₁ − ⋯ − C_l − R'`: for `l = 0`, `Q · H = 2` forces a type-(U3) configuration at the
  shortest curve `Q` (Proposition 6.2 (iii)); for `l ≥ 1`, the one-component replacement
  (Theorem 4.5) at `Q` with the excess contact `C₁` produces a datum with smaller Picard number
  and at least as many singular points, contradicting minimality.

The arithmetic of `Support/SectionCount.lean` is redone inline in inequality form (the lane
establishes `r_t − a_t ≤ 2 − s`, `r_t − a_t ≤ 1` and `#{(1,1)-fibres} ≤ s − 1` rather than the
equalities `r₀ − a₀ = 2 − s`, `#W = s − 1` that module assumes).

Main statements: `twoContactRulingBound` (explicit form) and `twoContactRulingHyp`
(`TwoContactRulingHyp R P`, the form consumed by Theorem 7.1).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicGeometry CategoryTheory Finset
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S03 KltDP.Manuscript.S04

universe u

namespace KltDP.Manuscript.S07

variable {k : Type u} [Field k] [IsAlgClosed k] {R : ResolutionDatum k}

/-! ### The fibre divisor `F = U + 2P + V` -/

section FibreDivisor

variable (U V : R.Vertices) (P : R.S.PrimeCurve)

theorem fibreDivisor_eq :
    R.fibreDivisor U V P = R.S.primeCurveCartier R.hreg U.val +
      (R.S.primeCurveCartier R.hreg P + R.S.primeCurveCartier R.hreg P) +
      R.S.primeCurveCartier R.hreg V.val := by
  unfold ResolutionDatum.fibreDivisor
  rw [two_zsmul]

theorem intersectionNumber_fibreDivisor (C : R.S.PrimeCurve) :
    C.intersectionNumber (R.fibreDivisor U V P) =
      C.intersectionNumber (R.S.primeCurveCartier R.hreg U.val) +
        (C.intersectionNumber (R.S.primeCurveCartier R.hreg P) +
          C.intersectionNumber (R.S.primeCurveCartier R.hreg P)) +
        C.intersectionNumber (R.S.primeCurveCartier R.hreg V.val) := by
  rw [fibreDivisor_eq, C.intersectionNumber_add, C.intersectionNumber_add,
    C.intersectionNumber_add]

/-- `D_i² = -2` for a weight-two vertex. -/
theorem selfInter_of_w_eq_two (i : R.Vertices) (hw : R.w i = 2) :
    i.val.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) = -2 := by
  have h := selfIntersection_eq_neg_w i
  rw [hw] at h
  have h' : i.val.selfIntersectionNumber R.hreg = -2 := by exact_mod_cast h
  exact h'

/-- `K_S · D_i = 0` for a weight-two vertex. -/
theorem Kdeg_eq_zero_of_w_eq_two (i : R.Vertices) (hw : R.w i = 2) : R.Kdeg i.val = 0 := by
  have h := R.Kdeg_exceptional i
  unfold ResolutionDatum.q at h
  rw [hw, sub_self] at h
  exact_mod_cast h

variable (hUV : U ≠ V) (hwU : R.w U = 2) (hwV : R.w V = 2) (hUVdisj : ¬ R.graph.Adj U V)
  (hPU : R.contact P U = 1) (hPV : R.contact P V = 1) (hP : R.IsExteriorMinusOne P)

include hUV hwU hUVdisj hPU in
theorem fibreDivisor_U : U.val.intersectionNumber (R.fibreDivisor U V P) = 0 := by
  rw [intersectionNumber_fibreDivisor]
  have h1 := selfInter_of_w_eq_two U hwU
  have h2 : U.val.intersectionNumber (R.S.primeCurveCartier R.hreg P) = 1 := by
    rw [inter_symm]; exact hPU
  have h3 : U.val.intersectionNumber (R.S.primeCurveCartier R.hreg V.val) = 0 :=
    contact_eq_zero_of_not_adj hUV hUVdisj
  rw [h1, h2, h3]; norm_num

include hUV hwV hUVdisj hPV in
theorem fibreDivisor_V : V.val.intersectionNumber (R.fibreDivisor U V P) = 0 := by
  rw [intersectionNumber_fibreDivisor]
  have h1 := selfInter_of_w_eq_two V hwV
  have h2 : V.val.intersectionNumber (R.S.primeCurveCartier R.hreg P) = 1 := by
    rw [inter_symm]; exact hPV
  have h3 : V.val.intersectionNumber (R.S.primeCurveCartier R.hreg U.val) = 0 :=
    contact_eq_zero_of_not_adj (Ne.symm hUV) (fun h => hUVdisj h.symm)
  rw [h1, h2, h3]; norm_num

include hPU hPV hP in
theorem fibreDivisor_P : P.intersectionNumber (R.fibreDivisor U V P) = 0 := by
  rw [intersectionNumber_fibreDivisor]
  have h1 : P.intersectionNumber (R.S.primeCurveCartier R.hreg P) = -1 := hP.1.selfIntersection
  have h2 : P.intersectionNumber (R.S.primeCurveCartier R.hreg U.val) = 1 := hPU
  have h3 : P.intersectionNumber (R.S.primeCurveCartier R.hreg V.val) = 1 := hPV
  rw [h1, h2, h3]; norm_num

include hUV hwU hwV hUVdisj hPU hPV hP in
theorem fibreDivisor_nonneg (C : R.S.PrimeCurve) :
    0 ≤ C.intersectionNumber (R.fibreDivisor U V P) := by
  by_cases hCU : C = U.val
  · rw [hCU, fibreDivisor_U U V P hUV hwU hUVdisj hPU]
  by_cases hCV : C = V.val
  · rw [hCV, fibreDivisor_V U V P hUV hwV hUVdisj hPV]
  by_cases hCP : C = P
  · rw [hCP, fibreDivisor_P U V P hPU hPV hP]
  rw [intersectionNumber_fibreDivisor]
  have h1 := inter_nonneg hCU
  have h2 := inter_nonneg hCV
  have h3 := inter_nonneg hCP
  omega

include hUV hwU hwV hUVdisj hPU hPV hP in
theorem fibreDivisor_nef : Positivity.IsNef R.S.structureMorphism
    (cartierDivisorInvertibleSheaf R.S.toScheme (R.fibreDivisor U V P)) := by
  rw [Positivity.isNef_iff_forall_primeCurve]
  intro C
  exact fibreDivisor_nonneg U V P hUV hwU hwV hUVdisj hPU hPV hP C

include hUV hwU hwV hUVdisj hPU hPV hP in
theorem fibreDivisor_sq :
    R.S.intersectionPairing R.hreg (R.fibreDivisor U V P) (R.fibreDivisor U V P) = 0 := by
  have hU : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg U.val)
      (R.fibreDivisor U V P) = 0 := by
    rw [R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
    exact fibreDivisor_U U V P hUV hwU hUVdisj hPU
  have hV : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg V.val)
      (R.fibreDivisor U V P) = 0 := by
    rw [R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
    exact fibreDivisor_V U V P hUV hwV hUVdisj hPV
  have hPP : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg P)
      (R.fibreDivisor U V P) = 0 := by
    rw [R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
    exact fibreDivisor_P U V P hPU hPV hP
  nth_rewrite 1 [fibreDivisor_eq]
  rw [R.S.intersectionPairing_add_left R.hreg, R.S.intersectionPairing_add_left R.hreg,
    R.S.intersectionPairing_add_left R.hreg, hU, hV, hPP]
  norm_num

include hwU hwV hP in
theorem fibreDivisor_KS : R.S.intersectionPairing R.hreg R.KS (R.fibreDivisor U V P) = -2 := by
  rw [fibreDivisor_eq, R.S.intersectionPairing_add_right R.hreg,
    R.S.intersectionPairing_add_right R.hreg, R.S.intersectionPairing_add_right R.hreg,
    R.S.intersectionPairing_primeCurve R.hreg, R.S.intersectionPairing_primeCurve R.hreg,
    R.S.intersectionPairing_primeCurve R.hreg]
  have hU : U.val.intersectionNumber R.KS = 0 := Kdeg_eq_zero_of_w_eq_two U hwU
  have hV : V.val.intersectionNumber R.KS = 0 := Kdeg_eq_zero_of_w_eq_two V hwV
  have hPK : P.intersectionNumber R.KS = -1 :=
    KltDP.Manuscript.S02.Kdeg_eq_neg_one_of_isMinusOne R P hP.1
  rw [hU, hV, hPK]
  norm_num

theorem fibreDivisor_Lnum :
    R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (NefNullCurveNegativeSquare.cartierClass R.S (R.fibreDivisor U V P)) = 2 * R.Ldeg P := by
  have hsplit : NefNullCurveNegativeSquare.cartierClass R.S (R.fibreDivisor U V P) =
      NefNullCurveNegativeSquare.cartierClass R.S (R.S.primeCurveCartier R.hreg U.val) +
        (NefNullCurveNegativeSquare.cartierClass R.S (R.S.primeCurveCartier R.hreg P) +
          NefNullCurveNegativeSquare.cartierClass R.S (R.S.primeCurveCartier R.hreg P)) +
        NefNullCurveNegativeSquare.cartierClass R.S (R.S.primeCurveCartier R.hreg V.val) := by
    rw [fibreDivisor_eq]
    show R.S.picardNumericalMap (cartierPicardHom R.S.toScheme (_ + _ + _)) = _
    rw [map_add, map_add, map_add, map_add, map_add, map_add]
    rfl
  rw [hsplit, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.add_right]
  have hU : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (NefNullCurveNegativeSquare.cartierClass R.S (R.S.primeCurveCartier R.hreg U.val)) = 0 := by
    change R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg U.val) = 0
    rw [KltDP.Manuscript.S02.Lnum_pairing_curveClass, R.Ldeg_exceptional U]
  have hV : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (NefNullCurveNegativeSquare.cartierClass R.S (R.S.primeCurveCartier R.hreg V.val)) = 0 := by
    change R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg V.val) = 0
    rw [KltDP.Manuscript.S02.Lnum_pairing_curveClass, R.Ldeg_exceptional V]
  have hPP : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (NefNullCurveNegativeSquare.cartierClass R.S (R.S.primeCurveCartier R.hreg P)) = R.Ldeg P := by
    change R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P) = _
    exact KltDP.Manuscript.S02.Lnum_pairing_curveClass R P
  rw [hU, hV, hPP]
  ring

end FibreDivisor

/-! ### The ruling: fibre patterns, sections and pieces -/

section Ruling

variable (p : ℕ) [CharP k p] (hp : 0 < p)
  (F : CartierDivisor R.S.toScheme)
  (hF : Positivity.IsNef R.S.structureMorphism (cartierDivisorInvertibleSheaf R.S.toScheme F))
  (hFF : R.S.intersectionPairing R.hreg F F = 0)
  (hKF : R.S.intersectionPairing R.hreg R.KS F = -2)
  (g : R.S.toScheme ⟶ projectiveSpace k 1)
  (hg : g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism)
  (e : (pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
    cartierDivisorModule R.S.toScheme F)
  (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
  (hL : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
    (NefNullCurveNegativeSquare.cartierClass R.S F) = 2 * R.Ldeg P)

include hg e in
/-- A horizontal curve differs from every fibre component. -/
theorem ne_of_horizontal_of_inFiber {H : R.Vertices} (hH : H.val.intersectionNumber F ≠ 0)
    {t : projectiveSpace k 1} {C : R.S.PrimeCurve} (hC : InFiber g t C) : H.val ≠ C := by
  intro heq
  apply hH
  rw [heq]
  exact intersectionNumber_eq_zero_of_vertical R F g hg e C t hC

/-- Components of different fibres are disjoint, hence have intersection number zero. -/
theorem inter_eq_zero_of_inFiber_ne {t t' : projectiveSpace k 1} (htt' : t ≠ t')
    {C C' : R.S.PrimeCurve} (hC : InFiber g t C) (hC' : InFiber g t' C') :
    C.intersectionNumber (R.S.primeCurveCartier R.hreg C') = 0 := by
  have hne : C ≠ C' := by
    intro h
    subst h
    exact htt' (inFiber_unique g hC hC')
  rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg]
  apply (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint R.S R.hreg
    C C' hne).mpr
  rw [Set.disjoint_left]
  intro x hx hx'
  exact htt' ((hC x hx).symm.trans (hC' x hx'))

include hp hFF hKF hg e in
/-- The set of reducible closed fibres, as a finset containing every fibre with a vertical
exceptional curve. -/
theorem exists_reducibleFibres [IsProper g] [Surjective g] :
    ∃ T : Finset (projectiveSpace k 1),
      (∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1))) ∧
      (∀ t ∈ T, ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') ∧
      (∀ (i : R.Vertices) (t : projectiveSpace k 1), InFiber g t i.val → t ∈ T) ∧
      (∀ t : projectiveSpace k 1, IsClosed ({t} : Set (projectiveSpace k 1)) →
        (∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') → t ∈ T) := by
  obtain ⟨hfin, -⟩ := rulingFibers_reducibleFibers_finite R p hp F hFF hKF g hg e
  refine ⟨hfin.toFinset, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hfin.mem_toFinset.mp ht).1
  · intro t ht
    exact (hfin.mem_toFinset.mp ht).2
  · intro i t hi
    obtain ⟨hcl, hred⟩ := inFiber_exceptional_closed_reducible F g hg e hFF hKF i t hi
    exact hfin.mem_toFinset.mpr ⟨hcl, hred⟩
  · intro t hcl hred
    exact hfin.mem_toFinset.mpr ⟨hcl, hred⟩

/-! #### Patterns `(2)` and `(1, 1)` and the count `o_t` -/

theorem numExterior_eq_two_of_pattern_one_one {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E) (R₁ R₂ : R.S.PrimeCurve)
    (hne : R₁ ≠ R₂) (h₁ : InFiber g t R₁) (h₂ : InFiber g t R₂)
    (hex₁ : ¬ IsExceptionalCurve R.π R₁) (hex₂ : ¬ IsExceptionalCurve R.π R₂)
    (huniq : ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₁ ∨ C = R₂) :
    numExterior g t = 2 := by
  classical
  rw [numExterior_eq_card F g hE, Finset.card_eq_two]
  refine ⟨R₁, R₂, hne, ?_⟩
  ext C
  rw [mem_exteriorSupport F g hE, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hC1, hC2⟩
    exact huniq C hC1 hC2
  · rintro (rfl | rfl)
    · exact ⟨h₁, hex₁⟩
    · exact ⟨h₂, hex₂⟩

theorem numExterior_eq_one_of_pattern_two {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E) (R₀ : R.S.PrimeCurve)
    (hR₀ : InFiber g t R₀) (hex : ¬ IsExceptionalCurve R.π R₀)
    (huniq : ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₀) :
    numExterior g t = 1 := by
  classical
  rw [numExterior_eq_card F g hE, Finset.card_eq_one]
  refine ⟨R₀, ?_⟩
  ext C
  rw [mem_exteriorSupport F g hE, Finset.mem_singleton]
  constructor
  · rintro ⟨hC1, hC2⟩
    exact huniq C hC1 hC2
  · rintro rfl
    exact ⟨hR₀, hex⟩

include hp hFF hKF hg e hrho hP hL in
/-- A reducible fibre with `o_t ≠ 2` has pattern `(2)`. -/
theorem pattern_two_of_numExterior_ne_two [IsProper g] [Surjective g] {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (hne : numExterior g t ≠ 2) :
    ∃ R₀ : R.S.PrimeCurve, InFiber g t R₀ ∧ ¬ IsExceptionalCurve R.π R₀ ∧
      R.S.cartierToWeilHom E R₀ = 2 ∧
      ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₀ := by
  rcases exterior_pattern p hp F hFF hKF g hg e hrho P hP hL hE hred with h |
    ⟨R₁, R₂, hne12, h₁, h₂, hex₁, hex₂, -, -, huniq⟩
  · exact h
  · exact absurd (numExterior_eq_two_of_pattern_one_one F g hE R₁ R₂ hne12 h₁ h₂ hex₁ hex₂ huniq)
      hne

include hp hFF hKF hg e hrho hP hL in
/-- A reducible fibre with `o_t = 2` has pattern `(1, 1)`. -/
theorem pattern_one_one_of_numExterior_eq_two [IsProper g] [Surjective g]
    {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (h2 : numExterior g t = 2) :
    ∃ R₁ R₂ : R.S.PrimeCurve, R₁ ≠ R₂ ∧ InFiber g t R₁ ∧ InFiber g t R₂ ∧
      ¬ IsExceptionalCurve R.π R₁ ∧ ¬ IsExceptionalCurve R.π R₂ ∧
      R.S.cartierToWeilHom E R₁ = 1 ∧ R.S.cartierToWeilHom E R₂ = 1 ∧
      ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₁ ∨ C = R₂ := by
  rcases exterior_pattern p hp F hFF hKF g hg e hrho P hP hL hE hred with
    ⟨R₀, hR₀, hex, -, huniq⟩ | h
  · exfalso
    have := numExterior_eq_one_of_pattern_two F g hE R₀ hR₀ hex huniq
    omega
  · exact h

/-! #### Sections meet the retained part of a pattern-`(2)` fibre -/

include hg e in
/-- In a pattern-`(2)` fibre (unique exterior component `R₀`), a horizontal vertex `H` disjoint
from `R₀` meets a retained exceptional component of the fibre. -/
theorem exists_adj_vertical_of_inter_exterior_eq_zero {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E) (R₀ : R.S.PrimeCurve)
    (huniq : ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₀)
    (H : R.Vertices) (hH : H.val.intersectionNumber F ≠ 0)
    (hHR₀ : H.val.intersectionNumber (R.S.primeCurveCartier R.hreg R₀) = 0) :
    ∃ j : R.Vertices, InFiber g t j.val ∧ R.graph.Adj H j := by
  classical
  have hHvert : ∀ C, InFiber g t C → H.val ≠ C := fun C hC =>
    ne_of_horizontal_of_inFiber F g hg e hH hC
  have hsum := fiber_intersection_eq R F g hE H.val
  unfold Finsupp.sum at hsum
  dsimp only at hsum
  have hex : ∃ C ∈ (R.S.cartierToWeilHom E).support,
      R.S.cartierToWeilHom E C * H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_eq_zero hcon] at hsum
    exact hH hsum
  obtain ⟨C, hCmem, hCne⟩ := hex
  have hCin : InFiber g t C := inFiber_of_coeff_ne_zero R F g hE C (Finsupp.mem_support_iff.mp hCmem)
  have hCR₀ : C ≠ R₀ := by
    intro h
    apply hCne
    rw [h, hHR₀, mul_zero]
  have hCexc : IsExceptionalCurve R.π C := Classical.byContradiction fun h => hCR₀ (huniq C hCin h)
  refine ⟨⟨C, hCexc⟩, hCin, ?_⟩
  have hne : H ≠ ⟨C, hCexc⟩ := fun h => hHvert C hCin (congrArg Subtype.val h)
  refine Classical.byContradiction fun hadj => hCne ?_
  have h0 := contact_eq_zero_of_not_adj hne hadj
  change H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0 at h0
  rw [h0, mul_zero]

include hg e in
/-- In a pattern-`(2)` fibre (unique exterior component `R₀` of multiplicity two), a section
`H` (`F · H = 1`) is disjoint from `R₀`. -/
theorem section_inter_exterior_eq_zero {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E) (R₀ : R.S.PrimeCurve)
    (hR₀ : InFiber g t R₀) (hμ : R.S.cartierToWeilHom E R₀ = 2)
    (H : R.Vertices) (hH : H.val.intersectionNumber F = 1) :
    H.val.intersectionNumber (R.S.primeCurveCartier R.hreg R₀) = 0 := by
  classical
  have hHvert : ∀ C, InFiber g t C → H.val ≠ C := fun C hC =>
    ne_of_horizontal_of_inFiber F g hg e (by rw [hH]; exact one_ne_zero) hC
  have hsum := fiber_intersection_eq R F g hE H.val
  rw [hH] at hsum
  unfold Finsupp.sum at hsum
  dsimp only at hsum
  have hnn : ∀ C ∈ (R.S.cartierToWeilHom E).support,
      0 ≤ R.S.cartierToWeilHom E C * H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) :=
    fun C hC => mul_nonneg (hE.effective C)
      (inter_nonneg (hHvert C (inFiber_of_coeff_ne_zero R F g hE C (Finsupp.mem_support_iff.mp hC))))
  have hR₀mem : R₀ ∈ (R.S.cartierToWeilHom E).support :=
    (inFiber_iff_mem_support R F g hE R₀).mp hR₀
  have h1 := Finset.single_le_sum hnn hR₀mem
  rw [hμ, ← hsum] at h1
  have h2 := inter_nonneg (hHvert R₀ hR₀)
  omega

include hg e in
/-- In a pattern-`(2)` fibre, a section meets a retained exceptional component. -/
theorem exists_adj_vertical_of_section {t : projectiveSpace k 1}
    {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E) (R₀ : R.S.PrimeCurve)
    (hR₀ : InFiber g t R₀) (hμ : R.S.cartierToWeilHom E R₀ = 2)
    (huniq : ∀ C, InFiber g t C → ¬ IsExceptionalCurve R.π C → C = R₀)
    (H : R.Vertices) (hH : H.val.intersectionNumber F = 1) :
    ∃ j : R.Vertices, InFiber g t j.val ∧ R.graph.Adj H j :=
  exists_adj_vertical_of_inter_exterior_eq_zero F g hg e hE R₀ huniq H (by rw [hH]; exact one_ne_zero)
    (section_inter_exterior_eq_zero F g hg e hE R₀ hR₀ hμ H hH)

/-- `a_t ≥ s` when every horizontal vertex meets a vertical vertex over `t`. -/
theorem numHorizontal_le_mixedIncidences (t : projectiveSpace k 1)
    (hall : ∀ H : R.Vertices, IsHorizontal g H →
      ∃ j : R.Vertices, InFiber g t j.val ∧ R.graph.Adj H j) :
    (numHorizontal g : ℤ) ≤ mixedIncidences g t := by
  classical
  rw [mixedIncidences_eq_sum]
  unfold numHorizontal
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  push_cast
  apply Finset.sum_le_sum
  intro H hH
  have hHhor : IsHorizontal g H := (Finset.mem_filter.mp hH).2
  obtain ⟨j, hj, hadj⟩ := hall H hHhor
  have hjmem : j ∈ Finset.univ.filter (fun j : R.Vertices => InFiber g t j.val) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hnn : ∀ j' ∈ Finset.univ.filter (fun j : R.Vertices => InFiber g t j.val),
      0 ≤ R.contact H.val j' := by
    intro j' hj'
    have hj'in : InFiber g t j'.val := (Finset.mem_filter.mp hj').2
    have hne : H.val ≠ j'.val := by
      intro h
      apply hHhor t
      rw [h]
      exact hj'in
    exact inter_nonneg hne
  calc (1 : ℤ) = R.contact H.val j := (contact_eq_one_of_adj hadj).symm
    _ ≤ _ := Finset.single_le_sum hnn hjmem

/-! #### Pattern `(1, 1)`: the retained part is connected -/

/-- Interior members of the chain are exceptional. -/
theorem chain_interior_exceptional (l : ℕ) (c : Fin (l + 2) → R.S.PrimeCurve)
    (hint : ∀ i : Fin (l + 2), i ≠ 0 → i ≠ Fin.last (l + 1) → IsExceptionalCurve R.π (c i))
    (m : ℕ) (hm : m < l + 2) (hm1 : 1 ≤ m) (hml : m ≤ l) : IsExceptionalCurve R.π (c ⟨m, hm⟩) := by
  have hz : ((0 : Fin (l + 2)) : ℕ) = 0 := Fin.val_zero (l + 1)
  have hlast : ((Fin.last (l + 1) : Fin (l + 2)) : ℕ) = l + 1 := Fin.val_last (l + 1)
  refine hint ⟨m, hm⟩ ?_ ?_
  · intro h
    have h' : m = 0 := by
      have := congrArg Fin.val h
      rw [hz] at this
      exact this
    omega
  · intro h
    have h' : m = l + 1 := by
      have := congrArg Fin.val h
      rw [hlast] at this
      exact this
    omega

/-- Intersection of a chain member with the last member `R₂ = c (l+1)`. -/
theorem chain_inter_last (l : ℕ) (c : Fin (l + 2) → R.S.PrimeCurve)
    (hcons : ∀ i j : Fin (l + 2), (i : ℕ) + 1 = j →
      (c i).intersectionNumber (R.S.primeCurveCartier R.hreg (c j)) = 1)
    (hnon : ∀ i j : Fin (l + 2), i ≠ j → (i : ℕ) + 1 ≠ j → (j : ℕ) + 1 ≠ i →
      (c i).intersectionNumber (R.S.primeCurveCartier R.hreg (c j)) = 0)
    (m : ℕ) (hm : m < l + 2) (hml : m ≤ l) :
    (c ⟨m, hm⟩).intersectionNumber (R.S.primeCurveCartier R.hreg (c (Fin.last (l + 1)))) =
      if m = l then 1 else 0 := by
  have hlast : ((Fin.last (l + 1) : Fin (l + 2)) : ℕ) = l + 1 := Fin.val_last (l + 1)
  split_ifs with h
  · exact hcons ⟨m, hm⟩ (Fin.last (l + 1)) (by rw [hlast]; show m + 1 = l + 1; omega)
  · refine hnon ⟨m, hm⟩ (Fin.last (l + 1)) ?_ ?_ ?_
    · intro heq
      have := congrArg Fin.val heq
      rw [hlast] at this
      change m = l + 1 at this
      omega
    · rw [hlast]
      show m + 1 ≠ l + 1
      omega
    · rw [hlast]
      show l + 1 + 1 ≠ m
      omega

/-- Intersection of the first member `R₁ = c 0` with a chain member. -/
theorem chain_inter_zero (l : ℕ) (c : Fin (l + 2) → R.S.PrimeCurve)
    (hcons : ∀ i j : Fin (l + 2), (i : ℕ) + 1 = j →
      (c i).intersectionNumber (R.S.primeCurveCartier R.hreg (c j)) = 1)
    (hnon : ∀ i j : Fin (l + 2), i ≠ j → (i : ℕ) + 1 ≠ j → (j : ℕ) + 1 ≠ i →
      (c i).intersectionNumber (R.S.primeCurveCartier R.hreg (c j)) = 0)
    (m : ℕ) (hm : m < l + 2) (hm1 : 1 ≤ m) :
    (c 0).intersectionNumber (R.S.primeCurveCartier R.hreg (c ⟨m, hm⟩)) =
      if m = 1 then 1 else 0 := by
  have hz : ((0 : Fin (l + 2)) : ℕ) = 0 := Fin.val_zero (l + 1)
  split_ifs with h
  · exact hcons 0 ⟨m, hm⟩ (by rw [hz]; show 0 + 1 = m; omega)
  · refine hnon 0 ⟨m, hm⟩ ?_ ?_ ?_
    · intro heq
      have := congrArg Fin.val heq
      rw [hz] at this
      change 0 = m at this
      omega
    · rw [hz]
      show 0 + 1 ≠ m
      omega
    · rw [hz]
      show m + 1 ≠ 0
      omega

/-- A vertical exceptional vertex of a pattern-`(1, 1)` fibre is an interior chain member. -/
theorem chain_index {t : projectiveSpace k 1} (l : ℕ) (c : Fin (l + 2) → R.S.PrimeCurve)
    (hall : ∀ C, InFiber g t C ↔ ∃ i, c i = C)
    (hext0 : ¬ IsExceptionalCurve R.π (c 0))
    (hextl : ¬ IsExceptionalCurve R.π (c (Fin.last (l + 1))))
    (i : R.Vertices) (hi : InFiber g t i.val) :
    ∃ (m : ℕ) (hm : m < l + 2), 1 ≤ m ∧ m ≤ l ∧ i.val = c ⟨m, hm⟩ := by
  have hz : ((0 : Fin (l + 2)) : ℕ) = 0 := Fin.val_zero (l + 1)
  have hlast : ((Fin.last (l + 1) : Fin (l + 2)) : ℕ) = l + 1 := Fin.val_last (l + 1)
  obtain ⟨j, hj⟩ := (hall i.val).mp hi
  refine ⟨j.val, j.isLt, ?_, ?_, ?_⟩
  · refine Classical.byContradiction fun h => ?_
    have hj0 : j = 0 := Fin.ext (by rw [hz]; omega)
    rw [hj0] at hj
    apply hext0
    rw [hj]
    exact i.property
  · refine Classical.byContradiction fun h => ?_
    have hjl : j = Fin.last (l + 1) := Fin.ext (by rw [hlast]; have := j.isLt; omega)
    rw [hjl] at hj
    apply hextl
    rw [hj]
    exact i.property
  · exact hj.symm.trans (congrArg c (Fin.ext rfl))

/-- In a pattern-`(1, 1)` fibre (a chain `R₁ − C₁ − ⋯ − C_l − R₂`), the exceptional vertical part
is a connected chain: `r_t ≤ 1`. -/
theorem numPieces_le_one_of_chain {t : projectiveSpace k 1}
    (l : ℕ) (c : Fin (l + 2) → R.S.PrimeCurve) (hinj : Function.Injective c)
    (hall : ∀ C, InFiber g t C ↔ ∃ i, c i = C)
    (hint : ∀ i : Fin (l + 2), i ≠ 0 → i ≠ Fin.last (l + 1) → IsExceptionalCurve R.π (c i))
    (hext0 : ¬ IsExceptionalCurve R.π (c 0))
    (hextl : ¬ IsExceptionalCurve R.π (c (Fin.last (l + 1))))
    (hcons : ∀ i j : Fin (l + 2), (i : ℕ) + 1 = j →
      (c i).intersectionNumber (R.S.primeCurveCartier R.hreg (c j)) = 1) :
    numPieces g t ≤ 1 := by
  classical
  have hz : ((0 : Fin (l + 2)) : ℕ) = 0 := Fin.val_zero (l + 1)
  have hlast : ((Fin.last (l + 1) : Fin (l + 2)) : ℕ) = l + 1 := Fin.val_last (l + 1)
  have hvert : ∀ (m : ℕ) (hm : m < l + 2), 1 ≤ m → m ≤ l →
      IsExceptionalCurve R.π (c ⟨m, hm⟩) := fun m hm hm1 hml =>
    chain_interior_exceptional l c hint m hm hm1 hml
  let S : Set R.Vertices := {i : R.Vertices | InFiber g t i.val}
  let vert : ∀ m : ℕ, 1 ≤ m → m ≤ l → S := fun m hm1 hml =>
    ⟨⟨c ⟨m, by omega⟩, hvert m (by omega) hm1 hml⟩, (hall _).mpr ⟨_, rfl⟩⟩
  have hstep : ∀ (m : ℕ) (hm1 : 1 ≤ m) (hml : m + 1 ≤ l),
      (R.graph.induce S).Adj (vert m hm1 (by omega)) (vert (m + 1) (by omega) hml) := by
    intro m hm1 hml
    have hne : c ⟨m, by omega⟩ ≠ c ⟨m + 1, by omega⟩ := by
      intro h
      have := hinj h
      rw [Fin.ext_iff] at this
      simp at this
    show R.graph.Adj ⟨c ⟨m, _⟩, _⟩ ⟨c ⟨m + 1, _⟩, _⟩
    refine ⟨fun h => hne (congrArg Subtype.val h), ?_⟩
    rw [← inter_pos_iff hne, hcons ⟨m, by omega⟩ ⟨m + 1, by omega⟩ rfl]
    exact one_pos
  have hreach : ∀ (m n : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) (hnl : n ≤ l),
      (R.graph.induce S).Reachable (vert m hm1 (by omega)) (vert n (by omega) hnl) := by
    intro m n hm1 hmn hnl
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · exact (ih (by omega) (by omega)).trans (hstep n (by omega) hnl).reachable
      · have hmn' : m = n + 1 := by omega
        subst hmn'
        exact SimpleGraph.Reachable.refl _
  have hindex : ∀ a : S, ∃ (m : ℕ) (hm1 : 1 ≤ m) (hml : m ≤ l), a = vert m hm1 hml := by
    intro a
    obtain ⟨i, hi⟩ := (hall a.1.1).mp a.2
    have hi0 : i ≠ 0 := by
      intro h
      apply hext0
      rw [← h, hi]
      exact a.1.2
    have hil : i ≠ Fin.last (l + 1) := by
      intro h
      apply hextl
      rw [← h, hi]
      exact a.1.2
    have h1 : 1 ≤ (i : ℕ) := by
      refine Classical.byContradiction fun h => hi0 ?_
      apply Fin.ext
      rw [hz]
      omega
    have hl : (i : ℕ) ≤ l := by
      refine Classical.byContradiction fun h => hil ?_
      apply Fin.ext
      rw [hlast]
      have := i.isLt
      omega
    refine ⟨i, h1, hl, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show a.1.1 = c ⟨i, _⟩
    exact (hi.symm.trans (congrArg c (Fin.ext rfl)))
  have hpre : (R.graph.induce S).Preconnected := by
    intro a b
    obtain ⟨ma, hma1, hmal, rfl⟩ := hindex a
    obtain ⟨mb, hmb1, hmbl, rfl⟩ := hindex b
    rcases le_or_lt ma mb with h | h
    · exact hreach ma mb hma1 h hmbl
    · exact (hreach mb ma hmb1 h.le hmal).symm
  have hsub := hpre.subsingleton_connectedComponent
  show Nat.card (R.graph.induce S).ConnectedComponent ≤ 1
  exact Finite.card_le_one_iff_subsingleton.mpr hsub

/-! #### The distinguished fibre `U + 2P + V` -/

include hp hFF hKF hg e in
/-- If `F = U + 2P + V` on prime curves and `P` lies in the fibre over `t`, every component of
that fibre is one of `U`, `V`, `P` (a component outside `{U, V, P}` is disjoint from all three,
and the fibre is connected). -/
theorem inFiber_distinguished [IsProper g] [Surjective g] (U V : R.Vertices)
    (hFdef : ∀ C : R.S.PrimeCurve, C.intersectionNumber F =
      C.intersectionNumber (R.S.primeCurveCartier R.hreg U.val) +
        (C.intersectionNumber (R.S.primeCurveCartier R.hreg P) +
          C.intersectionNumber (R.S.primeCurveCartier R.hreg P)) +
        C.intersectionNumber (R.S.primeCurveCartier R.hreg V.val))
    {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme} (hE : IsFiberDivisor F g t E)
    (hPt : InFiber g t P) (C : R.S.PrimeCurve) (hC : InFiber g t C) :
    C = U.val ∨ C = V.val ∨ C = P := by
  classical
  haveI : Finite {C : R.S.PrimeCurve // InFiber g t C} := finite_inFiber_of_isFiberDivisor F g hE
  have hconn := fiber_isConnected R p hp F hFF hKF g hg e t
  have hGconn : (fiberGraph g t).Connected := fiberGraph_connected R F g hE hconn
  have key : ∀ (a b : {C : R.S.PrimeCurve // InFiber g t C}) (w : (fiberGraph g t).Walk a b),
      ¬ (a.1 = U.val ∨ a.1 = V.val ∨ a.1 = P) → ¬ (b.1 = U.val ∨ b.1 = V.val ∨ b.1 = P) := by
    intro a b w
    induction w with
    | nil => exact id
    | @cons a x b h w' ih =>
      intro ha
      apply ih
      intro hx
      have haF : a.1.intersectionNumber F = 0 :=
        intersectionNumber_eq_zero_of_vertical R F g hg e a.1 t a.2
      rw [hFdef] at haF
      push_neg at ha
      have h1 := inter_nonneg ha.1
      have h2 := inter_nonneg ha.2.1
      have h3 := inter_nonneg ha.2.2
      have hpos : 0 < a.1.intersectionNumber (R.S.primeCurveCartier R.hreg x.1) :=
        inter_pos_of_adj g h
      rcases hx with hx | hx | hx <;> rw [hx] at hpos <;> omega
  obtain ⟨w⟩ := hGconn.preconnected ⟨C, hC⟩ ⟨P, hPt⟩
  by_contra hnot
  exact key _ _ w hnot (Or.inr (Or.inr rfl))

/-! ### Case A: every horizontal vertex is a section -/

include hp hFF hKF hg e hrho hP hL in
/-- **Theorem 7.5, all-section case** (manuscript lines 2258–2278): if every horizontal vertex
has `F · H = 1`, then `#π₀(D) ≤ 7`. -/
theorem count_le_seven_of_sections [IsProper g] [Surjective g]
    (T : Finset (projectiveSpace k 1))
    (hTcl : ∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)))
    (hTred : ∀ t ∈ T, ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (hTall : ∀ (i : R.Vertices) (t : projectiveSpace k 1), InFiber g t i.val → t ∈ T)
    (hsec : ∀ H : R.Vertices, IsHorizontal g H → H.val.intersectionNumber F = 1)
    (U V : R.Vertices)
    (hFdef : ∀ C : R.S.PrimeCurve, C.intersectionNumber F =
      C.intersectionNumber (R.S.primeCurveCartier R.hreg U.val) +
        (C.intersectionNumber (R.S.primeCurveCartier R.hreg P) +
          C.intersectionNumber (R.S.primeCurveCartier R.hreg P)) +
        C.intersectionNumber (R.S.primeCurveCartier R.hreg V.val))
    (t₀ : projectiveSpace k 1) (ht₀ : t₀ ∈ T) (hPt₀ : InFiber g t₀ P) :
    (Nat.card R.graph.ConnectedComponent : ℤ) ≤ 7 := by
  classical
  -- the distinguished fibre
  obtain ⟨E₀, hE₀⟩ := exists_isFiberDivisor R F g e t₀ (hTcl t₀ ht₀)
  have hred₀ := hTred t₀ ht₀
  have hcomp₀ : ∀ C, InFiber g t₀ C → C = U.val ∨ C = V.val ∨ C = P :=
    inFiber_distinguished p hp F hFF hKF g hg e P U V hFdef hE₀ hPt₀
  have huniq₀ : ∀ C, InFiber g t₀ C → ¬ IsExceptionalCurve R.π C → C = P := by
    intro C hC hCex
    rcases hcomp₀ C hC with h | h | h
    · exact absurd (h ▸ U.property) hCex
    · exact absurd (h ▸ V.property) hCex
    · exact h
  have hμP : R.S.cartierToWeilHom E₀ P = 2 := by
    rcases exterior_pattern p hp F hFF hKF g hg e hrho P hP hL hE₀ hred₀ with
      ⟨R₀, hR₀, hex, hμ, -⟩ | ⟨R₁, R₂, hne, h₁, h₂, hex₁, hex₂, -, -, -⟩
    · rw [huniq₀ R₀ hR₀ hex] at hμ
      exact hμ
    · exact absurd ((huniq₀ R₁ h₁ hex₁).trans (huniq₀ R₂ h₂ hex₂).symm) hne
  have hnum₀ : numExterior g t₀ = 1 :=
    numExterior_eq_one_of_pattern_two F g hE₀ P hPt₀ hP.1.2 huniq₀
  -- every section is adjacent to `U` or `V`
  have hadjUV : ∀ H : R.Vertices, IsHorizontal g H → R.graph.Adj H U ∨ R.graph.Adj H V := by
    intro H hH
    obtain ⟨j, hj, hadj⟩ :=
      exists_adj_vertical_of_section F g hg e hE₀ P hPt₀ hμP huniq₀ H (hsec H hH)
    rcases hcomp₀ j.val hj with h | h | h
    · left
      rw [← Subtype.ext h]
      exact hadj
    · right
      rw [← Subtype.ext h]
      exact hadj
    · exact absurd (h ▸ j.property) hP.1.2
  -- `s ≤ 6`
  have hs6 : numHorizontal g ≤ 6 := by
    unfold numHorizontal
    have hsub : (Finset.univ.filter fun i : R.Vertices => IsHorizontal g i) ⊆
        R.graph.neighborFinset U ∪ R.graph.neighborFinset V := by
      intro H hH
      rcases hadjUV H (Finset.mem_filter.mp hH).2 with h | h
      · exact Finset.mem_union_left _ ((R.graph.mem_neighborFinset U H).mpr h.symm)
      · exact Finset.mem_union_right _ ((R.graph.mem_neighborFinset V H).mpr h.symm)
    calc _ ≤ (R.graph.neighborFinset U ∪ R.graph.neighborFinset V).card :=
          Finset.card_le_card hsub
      _ ≤ (R.graph.neighborFinset U).card + (R.graph.neighborFinset V).card :=
          Finset.card_union_le _ _
      _ ≤ 6 := by
          have h1 := exceptionalValencyAtMostThree R U
          have h2 := exceptionalValencyAtMostThree R V
          rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]
          omega
  -- the per-fibre bounds
  have hbound : ∀ t ∈ T, (numPieces g t : ℤ) - mixedIncidences g t ≤
      if numExterior g t = 2 then (1 : ℤ) else (2 : ℤ) - numHorizontal g := by
    intro t ht
    obtain ⟨E, hE⟩ := exists_isFiberDivisor R F g e t (hTcl t ht)
    have hred := hTred t ht
    split_ifs with h2
    · obtain ⟨R₁, R₂, hne, h₁, h₂, hex₁, hex₂, hμ₁, hμ₂, huniq⟩ :=
        pattern_one_one_of_numExterior_eq_two p hp F hFF hKF g hg e hrho P hP hL hE hred h2
      obtain ⟨l, c, hc0, hcl, hinj, hall, -, hint, hcons, -⟩ :=
        pattern_one_one_chain p hp F hFF hKF g hg e hrho P hP hL hE hred R₁ R₂ hne h₁ h₂ hex₁ hex₂
          hμ₁ hμ₂ huniq
      have hr := numPieces_le_one_of_chain g l c hinj hall hint (by rw [hc0]; exact hex₁)
        (by rw [hcl]; exact hex₂) hcons
      have ha : (0 : ℤ) ≤ mixedIncidences g t := by positivity
      omega
    · obtain ⟨R₀, hR₀, hex, hμ, huniq⟩ :=
        pattern_two_of_numExterior_ne_two p hp F hFF hKF g hg e hrho P hP hL hE hred h2
      have hr := pattern_two_numPieces_le_two p hp F hFF hKF g hg e hE hred R₀ hR₀ hex hμ huniq
      have ha := numHorizontal_le_mixedIncidences g t (fun H hH =>
        exists_adj_vertical_of_section F g hg e hE R₀ hR₀ hμ huniq H (hsec H hH))
      omega
  -- the count
  have hcount := forestCount g T hTall
  have hW := card_twoExteriorFibres_le p hp F hFF hKF g hg e hrho P hP hL T hTcl hTred hTall
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun t => numExterior g t = 2)
    (fun t => (numPieces g t : ℤ) - mixedIncidences g t)
  rw [← hsplit] at hcount
  set s := numHorizontal g with hs
  set W := T.filter (fun t => numExterior g t = 2) with hWdef
  set O := T.filter (fun t => ¬ numExterior g t = 2) with hOdef
  have hWsum : ∑ t ∈ W, ((numPieces g t : ℤ) - mixedIncidences g t) ≤ W.card := by
    calc _ ≤ ∑ t ∈ W, (1 : ℤ) := Finset.sum_le_sum (fun t ht => by
            have := hbound t (Finset.mem_filter.mp ht).1
            rw [if_pos (Finset.mem_filter.mp ht).2] at this
            exact this)
      _ = W.card := by simp
  have hOsum : ∑ t ∈ O, ((numPieces g t : ℤ) - mixedIncidences g t) ≤ O.card * (2 - (s : ℤ)) := by
    calc _ ≤ ∑ t ∈ O, (2 - (s : ℤ)) := Finset.sum_le_sum (fun t ht => by
            have := hbound t (Finset.mem_filter.mp ht).1
            rw [if_neg (Finset.mem_filter.mp ht).2] at this
            exact this)
      _ = O.card * (2 - (s : ℤ)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hOpos : 1 ≤ O.card :=
    Finset.card_pos.mpr ⟨t₀, Finset.mem_filter.mpr ⟨ht₀, by rw [hnum₀]; norm_num⟩⟩
  have hq : (0 : ℤ) ≤ horizontalIncidences g := by positivity
  have hWcard : (W.card : ℤ) + 1 ≤ s := by exact_mod_cast hW
  have hs6' : (s : ℤ) ≤ 6 := by exact_mod_cast hs6
  rcases Nat.lt_or_ge s 2 with hs1 | hs2
  · -- `s = 1`: at most three reducible fibres, each contributing at most one
    have hs1' : s = 1 := by omega
    have hcard1 : (Finset.univ.filter fun i : R.Vertices => IsHorizontal g i).card = 1 := hs1'
    obtain ⟨H₀, hH₀⟩ := Finset.card_eq_one.mp hcard1
    have hH₀hor : IsHorizontal g H₀ := by
      have hmem : H₀ ∈ (Finset.univ.filter fun i : R.Vertices => IsHorizontal g i) := by
        rw [hH₀]
        exact Finset.mem_singleton_self H₀
      exact (Finset.mem_filter.mp hmem).2
    have hex : ∀ t ∈ O, ∃ j : R.Vertices, InFiber g t j.val ∧ R.graph.Adj H₀ j := by
      intro t ht
      have htT := (Finset.mem_filter.mp ht).1
      obtain ⟨E, hE⟩ := exists_isFiberDivisor R F g e t (hTcl t htT)
      obtain ⟨R₀, hR₀, hex, hμ, huniq⟩ := pattern_two_of_numExterior_ne_two p hp F hFF hKF g hg e
        hrho P hP hL hE (hTred t htT) (Finset.mem_filter.mp ht).2
      exact exists_adj_vertical_of_section F g hg e hE R₀ hR₀ hμ huniq H₀ (hsec H₀ hH₀hor)
    let jmap : projectiveSpace k 1 → R.Vertices := fun t =>
      if h : t ∈ O then Classical.choose (hex t h) else H₀
    have hjmap : ∀ t (h : t ∈ O), InFiber g t (jmap t).val ∧ R.graph.Adj H₀ (jmap t) := by
      intro t h
      simp only [jmap, dif_pos h]
      exact Classical.choose_spec (hex t h)
    have hO3 : O.card ≤ 3 := by
      calc O.card ≤ (R.graph.neighborFinset H₀).card := by
            refine Finset.card_le_card_of_injOn jmap ?_ ?_
            · intro t ht
              exact (R.graph.mem_neighborFinset H₀ (jmap t)).mpr (hjmap t ht).2
            · intro t ht t' ht' heq
              exact inFiber_unique g (hjmap t ht).1 (heq ▸ (hjmap t' ht').1)
        _ ≤ 3 := by
            rw [SimpleGraph.card_neighborFinset_eq_degree]
            exact exceptionalValencyAtMostThree R H₀
    have hO3' : (O.card : ℤ) ≤ 3 := by exact_mod_cast hO3
    rw [hcount, hs1']
    push_cast
    have : (O.card : ℤ) * (2 - ((1 : ℕ) : ℤ)) = O.card := by push_cast; ring
    rw [hs1'] at hOsum
    push_cast at hOsum
    linarith
  · -- `s ≥ 2`
    have hs2' : (2 : ℤ) ≤ s := by exact_mod_cast hs2
    have hOpos' : (1 : ℤ) ≤ O.card := by exact_mod_cast hOpos
    have hprod : (O.card : ℤ) * (2 - (s : ℤ)) ≤ 1 * (2 - (s : ℤ)) :=
      mul_le_mul_of_nonpos_right hOpos' (by linarith)
    rw [hcount]
    linarith

/-! ### Case B: a bisection exists -/

/-- The integer weights are `2` or `≥ 3`. -/
theorem w_eq_two_or_three_le' (i : R.Vertices) : R.w i = 2 ∨ 3 ≤ R.w i := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, R.w i = z := ⟨_, w_eq_intCast R i⟩
  have h2 := R.two_le_w i
  rw [hz] at h2 ⊢
  have h2' : (2 : ℤ) ≤ z := by exact_mod_cast h2
  rcases (by omega : z = 2 ∨ 3 ≤ z) with h3 | h3
  · left
    rw [h3]
    norm_num
  · right
    exact_mod_cast h3

include hp hF hFF hKF hg e hrho hP hL in
/-- **Theorem 7.5, bisection case** (manuscript lines 2280–2316): if some exceptional curve `H`
has `F · H = 2`, then `#Sing(X) ≤ 7` (in a minimal counterexample, for the fibre class
`F = U + 2P + V`). -/
theorem singularPoints_le_seven_of_bisection [IsProper g] [Surjective g] (hp2 : 2 < p)
    (hR : R.IsMinimalCounterexample)
    (T : Finset (projectiveSpace k 1))
    (hTcl : ∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)))
    (hTred : ∀ t ∈ T, ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C')
    (hTall : ∀ (i : R.Vertices) (t : projectiveSpace k 1), InFiber g t i.val → t ∈ T)
    (hTfull : ∀ t : projectiveSpace k 1, IsClosed ({t} : Set (projectiveSpace k 1)) →
      (∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') → t ∈ T)
    (U V : R.Vertices) (hUV : U ≠ V) (hwU : R.w U = 2) (hwV : R.w V = 2)
    (hUVdisj : ¬ R.graph.Adj U V) (hPU : R.contact P U = 1) (hPV : R.contact P V = 1)
    (hUF : U.val.intersectionNumber F = 0) (hVF : V.val.intersectionNumber F = 0)
    (hFdef : ∀ C : R.S.PrimeCurve, C.intersectionNumber F =
      C.intersectionNumber (R.S.primeCurveCartier R.hreg U.val) +
        (C.intersectionNumber (R.S.primeCurveCartier R.hreg P) +
          C.intersectionNumber (R.S.primeCurveCartier R.hreg P)) +
        C.intersectionNumber (R.S.primeCurveCartier R.hreg V.val))
    (H : R.Vertices) (hHF : H.val.intersectionNumber F = 2) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  have hcard := KltDP.Manuscript.S06.singularPoints_card_eq R
  have hforest : R.graph.IsAcyclic :=
    (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.2.1
  have hcount := forestCount g T hTall
  have hq : (0 : ℤ) ≤ horizontalIncidences g := by positivity
  have hp2' : p ≠ 2 := by omega
  obtain ⟨Z, hZ, hZD, hcases⟩ := bisectionAdjoint p hp F hF hFF hKF g hg e hrho P hP hL H hHF
  have hadjZ := fun C => adjoint_intersectionNumber F H Z hZD C
  -- if `H` is the only horizontal vertex: `s = 1` and no fibre has pattern `(1, 1)`
  have honly : (∀ T' : R.Vertices, T' ≠ H → T'.val.intersectionNumber F = 0) →
      numHorizontal g = 1 ∧ ∀ t ∈ T, numExterior g t ≠ 2 := by
    intro hT'
    have hs : numHorizontal g = 1 := by
      unfold numHorizontal
      rw [Finset.card_eq_one]
      refine ⟨H, ?_⟩
      ext i
      rw [Finset.mem_filter, Finset.mem_singleton, isHorizontal_iff F g hg e]
      constructor
      · rintro ⟨-, hi⟩
        exact Classical.byContradiction fun h => hi (hT' i h)
      · rintro rfl
        exact ⟨Finset.mem_univ _, by rw [hHF]; norm_num⟩
    refine ⟨hs, fun t ht h2 => ?_⟩
    have hW := card_twoExteriorFibres_le p hp F hFF hKF g hg e hrho P hP hL T hTcl hTred hTall
    rw [hs] at hW
    have hmem : t ∈ T.filter (fun t => numExterior g t = 2) := Finset.mem_filter.mpr ⟨ht, h2⟩
    have hpos := Finset.card_pos.mpr ⟨t, hmem⟩
    omega
  -- a pattern-`(2)` fibre all of whose retained curves are disjoint from `H` is a branch point
  have hram : ∀ t ∈ T, numExterior g t ≠ 2 →
      (∀ C : R.S.PrimeCurve, InFiber g t C → IsExceptionalCurve R.π C →
        H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0) →
      IsClosed ({t} : Set (projectiveSpace k 1)) ∧
        ∃ (E : CartierDivisor R.S.toScheme) (R₀ : R.S.PrimeCurve), IsFiberDivisor F g t E ∧
          InFiber g t R₀ ∧ H.val.intersectionNumber (R.S.primeCurveCartier R.hreg R₀) = 1 ∧
          ∀ C, InFiber g t C → C ≠ R₀ →
            H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0 := by
    intro t ht hne2 hzero
    obtain ⟨E, hE⟩ := exists_isFiberDivisor R F g e t (hTcl t ht)
    obtain ⟨R₀, hR₀, hex, hμ, huniq⟩ := pattern_two_of_numExterior_ne_two p hp F hFF hKF g hg e
      hrho P hP hL hE (hTred t ht) hne2
    have hother : ∀ C, InFiber g t C → C ≠ R₀ →
        H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0 := fun C hC hCR₀ =>
      hzero C hC (Classical.byContradiction fun h => hCR₀ (huniq C hC h))
    refine ⟨hTcl t ht, E, R₀, hE, hR₀, ?_, hother⟩
    have hsum := fiber_intersection_eq R F g hE H.val
    rw [hHF] at hsum
    unfold Finsupp.sum at hsum
    dsimp only at hsum
    have hR₀mem : R₀ ∈ (R.S.cartierToWeilHom E).support :=
      (inFiber_iff_mem_support R F g hE R₀).mp hR₀
    rw [Finset.sum_eq_single R₀ (fun C hC hCR₀ => by
        rw [hother C (inFiber_of_coeff_ne_zero R F g hE C (Finsupp.mem_support_iff.mp hC)) hCR₀,
          mul_zero])
      (fun h => absurd hR₀mem h), hμ] at hsum
    omega
  -- a pattern-`(2)` fibre contributes at most `2` to the count
  have hc2 : ∀ t ∈ T, numExterior g t ≠ 2 → (numPieces g t : ℤ) - mixedIncidences g t ≤ 2 := by
    intro t ht hne2
    obtain ⟨E, hE⟩ := exists_isFiberDivisor R F g e t (hTcl t ht)
    obtain ⟨R₀, hR₀, hex, hμ, huniq⟩ := pattern_two_of_numExterior_ne_two p hp F hFF hKF g hg e
      hrho P hP hL hE (hTred t ht) hne2
    have hr := pattern_two_numPieces_le_two p hp F hFF hKF g hg e hE (hTred t ht) R₀ hR₀ hex hμ huniq
    have ha : (0 : ℤ) ≤ mixedIncidences g t := by positivity
    omega
  rcases hcases with ⟨hZ0, -, honlyH⟩ | ⟨R', hZR', hR'ex, hR'm1, hR'F, hR'H, hKsq, hT⟩
  · -- **`N = 0`**: `H` is the only horizontal vertex; every retained curve is disjoint from `H`
    obtain ⟨hs, hne2⟩ := honly honlyH
    have hzero : ∀ t ∈ T, ∀ C, InFiber g t C → IsExceptionalCurve R.π C →
        H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0 := by
      intro t ht C hC hCexc
      have h := hadjZ C
      rw [hZ0, map_zero, C.intersectionNumber_zero] at h
      obtain ⟨E, hE⟩ := exists_isFiberDivisor R F g e t (hTcl t ht)
      have hK : C.intersectionNumber R.KS = 0 :=
        (fiber_degree_equalities p hp F hFF hKF g hg e hrho P hP hL hE (hTred t ht)).2.2 C hC hCexc
      have hCF := intersectionNumber_eq_zero_of_vertical R F g hg e C t hC
      rw [inter_symm]
      omega
    have hTcard : T.card ≤ 2 :=
      bisectionRamification_count p F g hg e H.val H.property hHF hp2'
        (riemannHurwitzDegreeTwo_of_instance p hp2 F g hg e H.val) T
        (fun t ht => hram t ht (hne2 t ht) (hzero t ht))
    have hsum : ∑ t ∈ T, ((numPieces g t : ℤ) - mixedIncidences g t) ≤ 2 * T.card := by
      calc _ ≤ ∑ t ∈ T, (2 : ℤ) := Finset.sum_le_sum (fun t ht => hc2 t ht (hne2 t ht))
        _ = 2 * T.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hTcard' : (T.card : ℤ) ≤ 2 := by exact_mod_cast hTcard
    rw [hcard]
    have : (Nat.card R.graph.ConnectedComponent : ℤ) ≤ 7 := by
      rw [hcount, hs]
      push_cast
      linarith
    exact_mod_cast this
  · -- **`N = R'`**
    obtain ⟨t₁, ht₁cl, hR't₁⟩ := exists_vertical_of_intersectionNumber_eq_zero R F g hg e R' hR'F
    obtain ⟨E₁, hE₁⟩ := exists_isFiberDivisor R F g e t₁ ht₁cl
    have hred₁ : ∃ C C' : R.S.PrimeCurve, InFiber g t₁ C ∧ InFiber g t₁ C' ∧ C ≠ C' := by
      refine Classical.byContradiction fun hnot => ?_
      push_neg at hnot
      have hirr : ∀ C', InFiber g t₁ C' → C' = R' := fun C' hC' => hnot C' R' hC' hR't₁
      have hsq := (irreducibleFiber_component R F hFF hKF g hE₁ R' hR't₁ hirr).2.2.1
      have := hR'm1.selfIntersection
      omega
    have ht₁T : t₁ ∈ T := hTfull t₁ ht₁cl hred₁
    -- the key identity `C · R' = K_S · C + F · C + H · C`
    have hkey : ∀ C : R.S.PrimeCurve, C.intersectionNumber (R.S.primeCurveCartier R.hreg R') =
        C.intersectionNumber R.KS + C.intersectionNumber F +
          C.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) := by
      intro C
      have h := hadjZ C
      rw [hZR', ← primeCurveCartier_eq_symm_single] at h
      exact h
    have hR'H0 : R'.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) = 0 := by
      have hne : R' ≠ H.val := fun h => hR'ex (h ▸ H.property)
      rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber
        R.S R.hreg]
      exact (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint R.S
        R.hreg R' H.val hne).mpr hR'H
    by_cases hother : ∀ T' : R.Vertices, T' ≠ H → T'.val.intersectionNumber F = 0
    · -- **`H` is the only horizontal vertex**
      obtain ⟨hs, hne2⟩ := honly hother
      have hzero : ∀ t ∈ T, t ≠ t₁ → ∀ C, InFiber g t C → IsExceptionalCurve R.π C →
          H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0 := by
        intro t ht htt₁ C hC hCexc
        have h := hkey C
        have hCR' : C.intersectionNumber (R.S.primeCurveCartier R.hreg R') = 0 :=
          inter_eq_zero_of_inFiber_ne g htt₁ hC hR't₁
        obtain ⟨E, hE⟩ := exists_isFiberDivisor R F g e t (hTcl t ht)
        have hK : C.intersectionNumber R.KS = 0 :=
          (fiber_degree_equalities p hp F hFF hKF g hg e hrho P hP hL hE (hTred t ht)).2.2 C hC
            hCexc
        have hCF := intersectionNumber_eq_zero_of_vertical R F g hg e C t hC
        rw [inter_symm]
        omega
      have hTcard : (T.erase t₁).card ≤ 2 :=
        bisectionRamification_count p F g hg e H.val H.property hHF hp2'
          (riemannHurwitzDegreeTwo_of_instance p hp2 F g hg e H.val) (T.erase t₁)
          (fun t ht => hram t (Finset.mem_of_mem_erase ht) (hne2 t (Finset.mem_of_mem_erase ht))
            (hzero t (Finset.mem_of_mem_erase ht) (Finset.ne_of_mem_erase ht)))
      -- the fibre of `R'` contributes at most `1`
      have hc₁ : (numPieces g t₁ : ℤ) - mixedIncidences g t₁ ≤ 1 := by
        obtain ⟨R₀, hR₀, hex, hμ, huniq⟩ := pattern_two_of_numExterior_ne_two p hp F hFF hKF g hg
          e hrho P hP hL hE₁ hred₁ (hne2 t₁ ht₁T)
        have hR₀R' : R₀ = R' := (huniq R' hR't₁ hR'ex).symm
        have hr := pattern_two_numPieces_le_two p hp F hFF hKF g hg e hE₁ hred₁ R₀ hR₀ hex hμ huniq
        have hHR₀ : H.val.intersectionNumber (R.S.primeCurveCartier R.hreg R₀) = 0 := by
          rw [hR₀R', inter_symm]
          exact hR'H0
        have ha := numHorizontal_le_mixedIncidences g t₁ (fun H' hH' => by
          have hH'H : H' = H := by
            refine Classical.byContradiction fun h => ?_
            exact hH' t₁ (Classical.byContradiction fun h' =>
              ((isHorizontal_iff F g hg e H').mp hH') (hother H' h))
          subst hH'H
          exact exists_adj_vertical_of_inter_exterior_eq_zero F g hg e hE₁ R₀ huniq H'
            (by rw [hHF]; norm_num) hHR₀)
        rw [hs] at ha
        push_cast at ha
        omega
      have hsum : ∑ t ∈ T, ((numPieces g t : ℤ) - mixedIncidences g t) ≤ 1 + 2 * (T.erase t₁).card := by
        rw [← Finset.add_sum_erase _ _ ht₁T]
        have h2 : ∑ t ∈ T.erase t₁, ((numPieces g t : ℤ) - mixedIncidences g t) ≤
            2 * (T.erase t₁).card := by
          calc _ ≤ ∑ t ∈ T.erase t₁, (2 : ℤ) := Finset.sum_le_sum (fun t ht =>
                hc2 t (Finset.mem_of_mem_erase ht) (hne2 t (Finset.mem_of_mem_erase ht)))
            _ = 2 * (T.erase t₁).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        linarith
      have hTcard' : ((T.erase t₁).card : ℤ) ≤ 2 := by exact_mod_cast hTcard
      rw [hcard]
      have : (Nat.card R.graph.ConnectedComponent : ℤ) ≤ 7 := by
        rw [hcount, hs]
        push_cast
        linarith
      exact_mod_cast this
    · -- **another horizontal vertex exists**
      push_neg at hother
      obtain ⟨T₀, hT₀H, hT₀F⟩ := hother
      obtain ⟨-, -, -, hμR'⟩ := hT T₀ hT₀H hT₀F
      have hμ1 : R.S.cartierToWeilHom E₁ R' = 1 := hμR' t₁ E₁ hE₁ hR't₁
      -- horizontal vertices other than `H` are disjoint from the fibre of `R'` away from `R'`
      have hTC : ∀ T' : R.Vertices, T' ≠ H → T'.val.intersectionNumber F ≠ 0 →
          ∀ C, InFiber g t₁ C → C ≠ R' →
            T'.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0 := by
        intro T' hT'H hT'F C hC hCR'
        obtain ⟨-, -, hTR', -⟩ := hT T' hT'H hT'F
        have hsum := fiber_intersection_eq R F g hE₁ T'.val
        unfold Finsupp.sum at hsum
        dsimp only at hsum
        have hnn : ∀ C' ∈ (R.S.cartierToWeilHom E₁).support,
            0 ≤ R.S.cartierToWeilHom E₁ C' *
              T'.val.intersectionNumber (R.S.primeCurveCartier R.hreg C') := fun C' hC' =>
          mul_nonneg (hE₁.effective C') (inter_nonneg (ne_of_horizontal_of_inFiber F g hg e hT'F
            (inFiber_of_coeff_ne_zero R F g hE₁ C' (Finsupp.mem_support_iff.mp hC'))))
        have hCmem := (inFiber_iff_mem_support R F g hE₁ C).mp hC
        have hR'mem := (inFiber_iff_mem_support R F g hE₁ R').mp hR't₁
        have h2 := Finset.add_le_sum hnn hCmem hR'mem hCR'
        rw [← hsum, hμ1, one_mul, ← hTR'] at h2
        have hμC := coeff_pos_of_inFiber R F g hE₁ C hC
        have hTC0 := inter_nonneg (ne_of_horizontal_of_inFiber F g hg e hT'F hC)
        have h3 := mul_le_mul_of_nonneg_right hμC hTC0
        omega
      rcases w_eq_two_or_three_le' H with hwH2 | hwH3
      · -- **`H² = -2`**: `K_S² = 1`, eight exceptional curves
        have hK1 : R.S.intersectionPairing R.hreg R.KS R.KS = 1 := by
          have h : (R.S.intersectionPairing R.hreg R.KS R.KS : ℚ) = 1 := by
            rw [hKsq, hwH2]
            norm_num
          exact_mod_cast h
        have hN : R.S.intersectionPairing R.hreg R.KS R.KS + (R.S.picardRank : ℤ) = 10 :=
          KltDP.Geometry.IsMinimalResolution.noetherRelation_of_kltDelPezzo R.hmin R.hDP R.hrank
            p hp R.KS R.eKS
        have hρ := R.hmin.picardRank_eq_of_klt R.hklt p hp
        rw [R.hrank] at hρ
        change R.S.picardRank = 1 + Nat.card R.Vertices at hρ
        have hV8 : Nat.card R.Vertices = 8 := by omega
        have hedges := KltDP.Support.WeightedForestCore.forest_natCard_edges R.graph hforest
        by_cases hedge : ∃ i j : R.Vertices, R.graph.Adj i j
        · obtain ⟨i, j, hij⟩ := hedge
          haveI : Nonempty R.graph.edgeSet := ⟨⟨s(i, j), hij⟩⟩
          have hpos : 0 < Nat.card R.graph.edgeSet := Nat.card_pos
          rw [hcard]
          omega
        · -- edge-free: `P` meets the three disjoint weight-two curves `U, V, H` once each
          push_neg at hedge
          have hUH : U ≠ H := by
            intro h
            rw [h, hHF] at hUF
            exact absurd hUF (by norm_num)
          have hVH : V ≠ H := by
            intro h
            rw [h, hHF] at hVF
            exact absurd hVF (by norm_num)
          have hHP : R.contact P H = 1 := by
            have h := hFdef H.val
            rw [hHF] at h
            have hHU := contact_eq_zero_of_not_adj (Ne.symm hUH) (hedge H U)
            change H.val.intersectionNumber (R.S.primeCurveCartier R.hreg U.val) = 0 at hHU
            have hHV := contact_eq_zero_of_not_adj (Ne.symm hVH) (hedge H V)
            change H.val.intersectionNumber (R.S.primeCurveCartier R.hreg V.val) = 0 at hHV
            rw [hHU, hHV] at h
            show P.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) = 1
            rw [inter_symm]
            omega
          rcases KltDP.Manuscript.S06Adj.threeContactDescent R P U V H hP.1 hUV hUH hVH hUVdisj
            (hedge U H) (hedge V H) hwU hwV hwH2 hPU hPV hHP p hp2 with h7 | ⟨Q, hQ, -, -, -, -, -, hQle⟩
          · exact h7
          · exfalso
            have h1 := hP.2 Q hQ
            have h2 := R.Lsq_pos
            linarith
      · -- **`H² ≤ -3`**: the fibre of `R'` is a chain `Q − C₁ − ⋯ − C_l − R'`
        have hne2₁ : numExterior g t₁ = 2 := by
          refine Classical.byContradiction fun hne => ?_
          obtain ⟨R₀, hR₀, hex, hμ, huniq⟩ := pattern_two_of_numExterior_ne_two p hp F hFF hKF g
            hg e hrho P hP hL hE₁ hred₁ hne
          rw [huniq R' hR't₁ hR'ex] at hμ1
          omega
        obtain ⟨R₁, R₂, hne12, h₁, h₂, hex₁, hex₂, hμ₁, hμ₂, huniq⟩ :=
          pattern_one_one_of_numExterior_eq_two p hp F hFF hKF g hg e hrho P hP hL hE₁ hred₁ hne2₁
        obtain ⟨Q, hQt₁, hQex, hQR', hμQ, huniqQ⟩ : ∃ Q : R.S.PrimeCurve, InFiber g t₁ Q ∧
            ¬ IsExceptionalCurve R.π Q ∧ Q ≠ R' ∧ R.S.cartierToWeilHom E₁ Q = 1 ∧
            ∀ C, InFiber g t₁ C → ¬ IsExceptionalCurve R.π C → C = Q ∨ C = R' := by
          rcases huniq R' hR't₁ hR'ex with h | h
          · refine ⟨R₂, h₂, hex₂, fun heq => hne12 (h.symm.trans heq.symm), hμ₂, fun C hC hCex => ?_⟩
            rcases huniq C hC hCex with h' | h'
            · right; rw [h', h]
            · left; exact h'
          · refine ⟨R₁, h₁, hex₁, fun heq => hne12 (heq.trans h), hμ₁, fun C hC hCex => ?_⟩
            rcases huniq C hC hCex with h' | h'
            · left; exact h'
            · right; rw [h', h]
        obtain ⟨l, c, hc0, hcl, hinj, hall, hμall, hint, hcons, hnon⟩ :=
          pattern_one_one_chain p hp F hFF hKF g hg e hrho P hP hL hE₁ hred₁ Q R' hQR' hQt₁ hR't₁
            hQex hR'ex hμQ hμ1 huniqQ
        have hext0 : ¬ IsExceptionalCurve R.π (c 0) := by rw [hc0]; exact hQex
        have hextl : ¬ IsExceptionalCurve R.π (c (Fin.last (l + 1))) := by rw [hcl]; exact hR'ex
        -- `Q` is a shortest exterior `(-1)`-curve
        obtain ⟨hQm1, hKQ⟩ :=
          exterior_component_isMinusOne p hp F hFF hKF g hg e hE₁ hred₁ Q hQt₁ hQex
        have hQext : R.IsExteriorMinusOne Q := ⟨hQm1, hQex⟩
        have hLQ : R.Ldeg Q = R.Ldeg P :=
          (fiber_degree_equalities p hp F hFF hKF g hg e hrho P hP hL hE₁ hred₁).2.1 Q hQt₁ hQex
        have hQshort : R.IsShortestExteriorMinusOne Q :=
          ⟨hQext, fun Q' hQ' => by rw [hLQ]; exact hP.2 Q' hQ'⟩
        have hQF : Q.intersectionNumber F = 0 := intersectionNumber_eq_zero_of_vertical R F g hg e Q t₁ hQt₁
        -- `Q · H = Q · R' + 1`
        have hQH : Q.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) =
            Q.intersectionNumber (R.S.primeCurveCartier R.hreg R') + 1 := by
          have h := hkey Q
          have hKQ' : Q.intersectionNumber R.KS = -1 := hKQ
          rw [hKQ', hQF] at h
          omega
        -- `Q · R' = [l = 0]`
        have hQR'val : Q.intersectionNumber (R.S.primeCurveCartier R.hreg R') =
            if (0 : ℕ) = l then 1 else 0 := by
          rw [← hc0, ← hcl]
          exact chain_inter_last l c hcons hnon 0 (by omega) (by omega)
        -- interior chain members: exceptional, with `C · H = C · R'`
        have hint' : ∀ (m : ℕ) (hm : m < l + 2), 1 ≤ m → m ≤ l → IsExceptionalCurve R.π (c ⟨m, hm⟩) :=
          fun m hm hm1 hml => chain_interior_exceptional l c hint m hm hm1 hml
        have hcin : ∀ (m : ℕ) (hm : m < l + 2), InFiber g t₁ (c ⟨m, hm⟩) := fun m hm =>
          (hall _).mpr ⟨_, rfl⟩
        have hcH : ∀ (m : ℕ) (hm : m < l + 2), 1 ≤ m → m ≤ l →
            (c ⟨m, hm⟩).intersectionNumber (R.S.primeCurveCartier R.hreg H.val) =
              (c ⟨m, hm⟩).intersectionNumber (R.S.primeCurveCartier R.hreg R') := by
          intro m hm hm1 hml
          have h := hkey (c ⟨m, hm⟩)
          have hK : (c ⟨m, hm⟩).intersectionNumber R.KS = 0 :=
            (fiber_degree_equalities p hp F hFF hKF g hg e hrho P hP hL hE₁ hred₁).2.2 _ (hcin m hm)
              (hint' m hm hm1 hml)
          have hF0 := intersectionNumber_eq_zero_of_vertical R F g hg e _ t₁ (hcin m hm)
          omega
        have hcR' : ∀ (m : ℕ) (hm : m < l + 2), m ≤ l →
            (c ⟨m, hm⟩).intersectionNumber (R.S.primeCurveCartier R.hreg R') =
              if m = l then 1 else 0 := by
          intro m hm hml
          rw [← hcl]
          exact chain_inter_last l c hcons hnon m hm hml
        have hQc : ∀ (m : ℕ) (hm : m < l + 2), 1 ≤ m →
            Q.intersectionNumber (R.S.primeCurveCartier R.hreg (c ⟨m, hm⟩)) =
              if m = 1 then 1 else 0 := by
          intro m hm hm1
          rw [← hc0]
          exact chain_inter_zero l c hcons hnon m hm hm1
        -- any contact of `Q` other than `H` is a vertical vertex over `t₁`
        have hQC : ∀ i : R.Vertices, i ≠ H → R.contact Q i ≠ 0 → InFiber g t₁ i.val := by
          intro i hiH hQi
          by_cases hiF : i.val.intersectionNumber F = 0
          · obtain ⟨t, -, hit⟩ := exists_vertical_of_intersectionNumber_eq_zero R F g hg e i.val hiF
            by_cases htt : t = t₁
            · rw [← htt]
              exact hit
            · exfalso
              apply hQi
              show Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) = 0
              exact inter_eq_zero_of_inFiber_ne g (Ne.symm htt) hQt₁ hit
          · exfalso
            apply hQi
            show Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) = 0
            rw [inter_symm]
            exact hTC i hiH hiF Q hQt₁ hQR'
        have hQchain : ∀ i : R.Vertices, InFiber g t₁ i.val →
            ∃ (m : ℕ) (hm : m < l + 2), 1 ≤ m ∧ m ≤ l ∧ i.val = c ⟨m, hm⟩ :=
          fun i hi => chain_index g l c hall hext0 hextl i hi
        rcases Nat.eq_zero_or_pos l with hl0 | hlpos
        · -- **`l = 0`**: `Q · H = 2`, so `H² = -3` and `(U3)` at `Q`
          have hQH2 : R.contact Q H = 2 := by
            show Q.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) = 2
            rw [hQH, hQR'val, if_pos hl0.symm]
            norm_num
          have hotherQ : ∀ i : R.Vertices, i ≠ H → R.contact Q i = 0 := by
            intro i hiH
            refine Classical.byContradiction fun hQi => ?_
            obtain ⟨m, hm, hm1, hml, -⟩ := hQchain i (hQC i hiH hQi)
            omega
          have hwH3' : R.w H = 3 := by
            rcases isExcessContact_or_isBoundedContact R Q H with hex | hbd
            · exact (higher_weight_excess_contact R Q hQext H hwH3 hex).1
            · exfalso
              have := bounded_contact_simple R Q hQext H (by rw [hQH2]; norm_num) hbd
              rw [hQH2] at this
              exact absurd this (by norm_num)
          exact KltDP.Manuscript.S06.squareOneBound_U3 R p hp2 Q hQshort H hwH3' hQH2 hotherQ
        · -- **`l ≥ 1`**: one-component replacement at `Q` with `C = C₁`
          have hQR'0 : Q.intersectionNumber (R.S.primeCurveCartier R.hreg R') = 0 := by
            rw [hQR'val, if_neg (by omega)]
          have hQH1 : R.contact Q H = 1 := by
            show Q.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) = 1
            rw [hQH, hQR'0]
            norm_num
          have h1lt : 1 < l + 2 := by omega
          set C₁ : R.Vertices := ⟨c ⟨1, h1lt⟩, hint' 1 h1lt le_rfl hlpos⟩ with hC₁def
          have hC₁H : C₁ ≠ H := by
            intro h
            have := ne_of_horizontal_of_inFiber F g hg e (by rw [hHF]; norm_num) (hcin 1 h1lt)
            exact this (by rw [← h])
          have hQC₁ : R.contact Q C₁ = 1 := by
            show Q.intersectionNumber (R.S.primeCurveCartier R.hreg (c ⟨1, h1lt⟩)) = 1
            rw [hQc 1 h1lt le_rfl, if_pos rfl]
          have hwC₁ : R.w C₁ = 2 :=
            (vertical_exceptional_w_eq_two p hp F hFF hKF g hg e hrho P hP hL hE₁ hred₁ C₁
              (hcin 1 h1lt)).1
          have hotherQ : ∀ i : R.Vertices, i ≠ C₁ → i ≠ H → R.contact Q i = 0 := by
            intro i hiC₁ hiH
            refine Classical.byContradiction fun hQi => ?_
            obtain ⟨m, hm, hm1, hml, hi⟩ := hQchain i (hQC i hiH hQi)
            by_cases hm1' : m = 1
            · apply hiC₁
              apply Subtype.ext
              rw [hi, hC₁def]
              subst hm1'
              rfl
            · apply hQi
              show Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) = 0
              rw [hi, hQc m hm hm1, if_neg hm1']
          -- Theorem 4.5 at `Q` with the excess contact `C₁`
          have hexC : IsExcessContact R Q C₁ := by
            unfold IsExcessContact ResolutionDatum.q
            rw [contactVector_eq, hQC₁, hwC₁]
            norm_num
          have hbdd : ∀ i : R.Vertices, i ≠ C₁ → IsBoundedContact R Q i := by
            intro i hiC₁
            unfold IsBoundedContact ResolutionDatum.q
            rw [contactVector_eq]
            by_cases hiH : i = H
            · subst hiH
              rw [hQH1]
              push_cast
              linarith
            · rw [hotherQ i hiC₁ hiH]
              have := R.two_le_w i
              push_cast
              linarith
          -- the retained family `Q + (D − C₁)` is a forest: `Q` is a leaf attached to `H`
          have hacyclic : (curveIncidenceGraph (Replacement.famG R C₁ Q)).IsAcyclic := by
            let φ : Replacement.D0 R C₁ ⊕ Unit → R.Vertices := Sum.elim (fun i => i.1) (fun _ => C₁)
            have hφinj : Function.Injective φ := by
              rintro (i | u) (j | u') h
              · exact congrArg Sum.inl (Subtype.ext h)
              · exact absurd h i.2
              · exact absurd h.symm j.2
              · cases u; cases u'; rfl
            have hHac : (R.graph.comap φ).IsAcyclic := by
              intro v c' hc'
              exact hforest (c'.map (⟨φ, fun h => h⟩ : R.graph.comap φ →g R.graph)) (hc'.map hφinj)
            have hHC₁ : H ≠ C₁ := Ne.symm hC₁H
            refine isAcyclic_of_leaf (Sum.inr ()) (Sum.inl ⟨H, hHC₁⟩) ?_ (R.graph.comap φ) ?_ hHac
            · rintro (i | u) hadj
              · obtain ⟨-, hmeet⟩ := hadj
                have hne : Q ≠ i.1.1 := fun h => hQex (h ▸ i.1.property)
                have hpos : 0 < Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1.1) :=
                  (inter_pos_iff hne).mpr hmeet
                have hiH : i.1 = H := by
                  refine Classical.byContradiction fun h => ?_
                  have h0 := hotherQ i.1 i.2 h
                  change Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1.1) = 0 at h0
                  omega
                congr 1
                exact Subtype.ext hiH
              · exact absurd hadj (SimpleGraph.irrefl _)
            · rintro (i | u) (j | u') hadj ha hb
              · obtain ⟨hne, hmeet⟩ := hadj
                show R.graph.Adj i.1 j.1
                exact ⟨fun h => hne (by rw [Subtype.ext h]), hmeet⟩
              · exact absurd rfl (by cases u'; exact hb)
              · exact absurd rfl (by cases u; exact ha)
              · exact absurd rfl (by cases u; exact ha)
          obtain ⟨R₁', hρ, hcase0, hcase1⟩ :=
            Replacement.oneComponentReplacement_datum_cases R C₁ Q p hp hQext hexC hbdd hacyclic
          -- `a ≤ 1` (only `H`) and `deg C₁ ≥ 1`
          have hcc : Replacement.contactCount R C₁ Q ≤ 1 := by
            unfold Replacement.contactCount
            rw [Finset.card_le_one]
            intro a ha b hb
            have haH : a.1 = H := by
              refine Classical.byContradiction fun h => (Finset.mem_filter.mp ha).2 ?_
              show KltDP.Manuscript.S02.contactVector R Q a.1 = 0
              rw [contactVector_eq, hotherQ a.1 a.2 h]
              simp
            have hbH : b.1 = H := by
              refine Classical.byContradiction fun h => (Finset.mem_filter.mp hb).2 ?_
              show KltDP.Manuscript.S02.contactVector R Q b.1 = 0
              rw [contactVector_eq, hotherQ b.1 b.2 h]
              simp
            exact Subtype.ext (haH.trans hbH.symm)
          have hdeg : 1 ≤ R.graph.degree C₁ := by
            rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, SimpleGraph.degree_pos_iff_exists_adj]
            rcases Nat.lt_or_ge l 2 with hl1 | hl2
            · -- `l = 1`: the neighbour is `H`
              have hl1' : l = 1 := by omega
              refine ⟨H, hC₁H, ?_⟩
              have hpos : 0 < (c ⟨1, h1lt⟩).intersectionNumber (R.S.primeCurveCartier R.hreg H.val) := by
                rw [hcH 1 h1lt le_rfl hlpos, hcR' 1 h1lt hlpos, if_pos hl1'.symm]
                norm_num
              exact (inter_pos_iff (fun h => hC₁H (Subtype.ext h))).mp hpos
            · -- `l ≥ 2`: the neighbour is `C₂`
              have h2lt : 2 < l + 2 := by omega
              refine ⟨⟨c ⟨2, h2lt⟩, hint' 2 h2lt (by omega) hl2⟩, ?_⟩
              have hne : c ⟨1, h1lt⟩ ≠ c ⟨2, h2lt⟩ := by
                intro h
                have := hinj h
                rw [Fin.ext_iff] at this
                simp at this
              refine ⟨fun h => hne (congrArg Subtype.val h), ?_⟩
              have hpos : 0 < (c ⟨1, h1lt⟩).intersectionNumber (R.S.primeCurveCartier R.hreg (c ⟨2, h2lt⟩)) := by
                rw [hcons ⟨1, h1lt⟩ ⟨2, h2lt⟩ rfl]
                norm_num
              exact (inter_pos_iff hne).mp hpos
          have h8 := hR.1
          have hR₁ : 7 < R₁'.X.singularPoints.card := by
            rcases Nat.eq_zero_or_pos (Replacement.contactCount R C₁ Q) with h0 | hpos
            · have := hcase0 h0
              omega
            · have := hcase1 hpos
              omega
          exact absurd (hR.2 R₁' hR₁) (not_le.mpr hρ)

end Ruling

/-! ### Theorem 7.5 -/

/-- **Manuscript Theorem 7.5** (`thm:two-contact-ruling`, lines 2236–2316), explicit form: for a
minimal counterexample in characteristic `p > 2`, a shortest exterior `(-1)`-curve `P` and two
disjoint weight-two exceptional curves `U, V` meeting `P` once each, if every exceptional curve has
degree at most two against the fibre class `F = U + 2P + V`, then `X` has at most seven singular
points. -/
theorem twoContactRulingBound (R : ResolutionDatum k) (p : ℕ) [CharP k p] (hp : 2 < p)
    (hR : R.IsMinimalCounterexample) (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (U V : R.Vertices) (hUV : U ≠ V) (hwU : R.w U = 2) (hwV : R.w V = 2)
    (hUVdisj : ¬ R.graph.Adj U V) (hPU : R.contact P U = 1) (hPV : R.contact P V = 1)
    (hdeg : ∀ i : R.Vertices, (i.val).intersectionNumber (R.fibreDivisor U V P) ≤ 2) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  have hp0 : 0 < p := by omega
  have hF := fibreDivisor_nef U V P hUV hwU hwV hUVdisj hPU hPV hP.1
  have hFF := fibreDivisor_sq U V P hUV hwU hwV hUVdisj hPU hPV hP.1
  have hKF := fibreDivisor_KS U V P hwU hwV hP.1
  have hL := fibreDivisor_Lnum U V P
  have hrho : 2 < R.S.picardRank := by
    have := (ResolutionDatum.IsMinimalCounterexample.canonicalSquare_le_one_and_picardRank R hR p
      hp0).2
    omega
  have hUF := fibreDivisor_U U V P hUV hwU hUVdisj hPU
  have hVF := fibreDivisor_V U V P hUV hwV hUVdisj hPV
  have hPF := fibreDivisor_P U V P hPU hPV hP.1
  have hFdef := intersectionNumber_fibreDivisor U V P
  obtain ⟨g, hg, hproper, hsurj, -, -, -, ⟨e⟩, -, -⟩ :=
    primitiveSquareZero_ruling R p hp0 (R.fibreDivisor U V P) hF hFF hKF
  haveI := hproper
  haveI := hsurj
  obtain ⟨T, hTcl, hTred, hTall, hTfull⟩ :=
    exists_reducibleFibres p hp0 (R.fibreDivisor U V P) hFF hKF g hg e
  by_cases hbis : ∃ H : R.Vertices, H.val.intersectionNumber (R.fibreDivisor U V P) = 2
  · -- a bisection exists
    obtain ⟨H, hHF⟩ := hbis
    exact singularPoints_le_seven_of_bisection p hp0 (R.fibreDivisor U V P) hF hFF hKF g hg e hrho
      P hP hL hp hR T hTcl hTred hTall hTfull U V hUV hwU hwV hUVdisj hPU hPV hUF hVF hFdef H hHF
  · -- every horizontal vertex is a section
    push_neg at hbis
    have hsec : ∀ H : R.Vertices, IsHorizontal g H →
        H.val.intersectionNumber (R.fibreDivisor U V P) = 1 := by
      intro H hH
      have hne := (isHorizontal_iff (R.fibreDivisor U V P) g hg e H).mp hH
      have h0 := intersectionNumber_nonneg R (R.fibreDivisor U V P) hF H.val
      have h2 := hdeg H
      have h2' := hbis H
      omega
    obtain ⟨t₀, ht₀cl, hPt₀⟩ :=
      exists_vertical_of_intersectionNumber_eq_zero R (R.fibreDivisor U V P) g hg e P hPF
    have hUt₀ : InFiber g t₀ U.val := by
      obtain ⟨tU, -, hUtU⟩ :=
        exists_vertical_of_intersectionNumber_eq_zero R (R.fibreDivisor U V P) g hg e U.val hUF
      have hne : U.val ≠ P := fun h => hP.1.2 (h ▸ U.property)
      have hpos : 0 < U.val.intersectionNumber (R.S.primeCurveCartier R.hreg P) := by
        rw [inter_symm]
        show 0 < R.contact P U
        rw [hPU]
        norm_num
      obtain ⟨x, hxU, hxP⟩ := (inter_pos_iff hne).mp hpos
      have htt : tU = t₀ := (hUtU x hxU).symm.trans (hPt₀ x hxP)
      rw [← htt]
      exact hUtU
    have hred₀ : ∃ C C' : R.S.PrimeCurve, InFiber g t₀ C ∧ InFiber g t₀ C' ∧ C ≠ C' :=
      ⟨U.val, P, hUt₀, hPt₀, fun h => hP.1.2 (h ▸ U.property)⟩
    have ht₀T : t₀ ∈ T := hTfull t₀ ht₀cl hred₀
    have hcount := count_le_seven_of_sections p hp0 (R.fibreDivisor U V P) hFF hKF g hg e hrho P hP
      hL T hTcl hTred hTall hsec U V hFdef t₀ ht₀T hPt₀
    rw [KltDP.Manuscript.S06.singularPoints_card_eq R]
    exact_mod_cast hcount

/-- **Manuscript Theorem 7.5** in the form consumed by Theorem 7.1 (`TwoContactRulingHyp`). -/
theorem twoContactRulingHyp (R : ResolutionDatum k) (p : ℕ) [CharP k p] (hp : 2 < p)
    (hR : R.IsMinimalCounterexample) (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P) :
    TwoContactRulingHyp R P :=
  fun U V hUV hwU hwV hUVdisj hPU hPV hdeg =>
    twoContactRulingBound R p hp hR P hP U V hUV hwU hwV hUVdisj hPU hPV hdeg

end KltDP.Manuscript.S07

#print axioms KltDP.Manuscript.S07.count_le_seven_of_sections
#print axioms KltDP.Manuscript.S07.singularPoints_le_seven_of_bisection
#print axioms KltDP.Manuscript.S07.twoContactRulingBound
#print axioms KltDP.Manuscript.S07.twoContactRulingHyp
