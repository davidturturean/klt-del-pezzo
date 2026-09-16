import KltDP.Examples.FrobeniusTowerGraphPuncture

/-!
# The Cartier identity `π^*Γ = B̃ + Σ_j E_j^tot` on the origin contact tower

Item 3 of BRIEF38, completing the `B` row of Proposition 10.1.  On stage `N+1` of the origin contact
tower the total transform `totalGraphDivisor (N+1) (m+(N+1))` of the graph `Γ : v = u^{m+N+1}`
(`FrobeniusTowerGraphPullback`) equals, as an effective Cartier divisor,

  `B̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P`

(`totalGraphDivisor_eq`), with `B̃ = graphStrictDivisor (N+1) m` of `FrobeniusGraphStrictCartier`.
The route is the accepted one for the fibre (`totalFiberDivisor_eq`): by `cartierDivisorOfIdeal_tower`
and the uniqueness `eq_cartierDivisorOfIdeal` it reduces to the identity of ideal-sheaf data
`totalGraphIdeal (n) (m+n) = graphTowerRHS n m` (`totalGraphIdeal_eq`), proved by induction over the
stages and locality on affine opens.

**The cover is not the accepted `coverOpen`.**  That cover splits the centre complement over the four
product charts `productOpen i j` of `P¹ × P¹`, which works for the fibre because the fibre has a
regular equation on each of the four.  The graph does not: `graphIdeal_locallyPrincipalRegular` is
proved against the accepted `comparisonOpen` cover (the two diagonal opens, where the generator is
`diagonalSection p i`, and the two companion opens `D(1 - u^p v)`, which miss the graph), so on a
mixed product chart there is no chosen regular chart of `graphZeroDivisor` at all.  Rather than
assert one, the centre-complement pieces of `graphCoverOpen` are indexed by the **points of the
base**, each carrying the chart that `graphIdeal_locallyPrincipalRegular` supplies at that point
(`graphBaseChart`, `graphChartAt`): the covering property is then immediate from `x ∈ U_x`, and the
chart's nonemptiness comes with it.  This is why `graph_puncture_case` is stated generically in a
chart.

Stage `0` is proved chart-wise (`graph_zero_case`) rather than through a generic `pullbackDivisor_id`,
which the accepted tree does not have: `between (Nat.zero_le 0)` is the identity by `between_refl`,
so the pulled-back coefficient is the plain restriction of the chart's generator and the accepted
`PrincipalRegularChart.restrict_span_eq` identifies the two ideals.  This is the same manoeuvre the
accepted `zero_case` makes for the fibre.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerGraphIdentity

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusExceptionalCartier FrobeniusExceptionalFinalConfiguration
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusGraphPicardClassAffine FrobeniusGraphPicardClassIntegral
open FrobeniusGraphStrictCartier FrobeniusGraphZeroCartier
open FrobeniusOldExceptionalLaterCartier
open FrobeniusStrictTransformClassesTower
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductCover
open FrobeniusStrictTransformSecondChartFrame FrobeniusStrictTransformStepPuncture
open FrobeniusTowerCartierIdentity
open FrobeniusTowerGraphCases FrobeniusTowerGraphPullback FrobeniusTowerGraphPuncture

variable {k : Type u} [Field k]

local instance graphIdentityProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance graphIdentityInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

/-! ### A chosen regular chart of the graph divisor at every point of the base -/

/-- At every point of `P¹ × P¹` the graph ideal has a principal regular chart containing it. -/
theorem exists_graphPrincipalChart (p : ℕ) (x : projectiveProduct k) :
    ∃ c : PrincipalRegularChart (projectiveProduct k) (graphIdeal p), x ∈ c.openSet.1 := by
  obtain ⟨U, hxU, d, hd, hdr⟩ := graphIdeal_locallyPrincipalRegular (k := k) p x
  exact ⟨⟨U, ⟨⟨x, hxU⟩⟩, d, hd, hdr⟩, hxU⟩

/-- The chosen principal regular chart of the graph ideal at a point of the base. -/
def graphBaseChart (p : ℕ) (x : projectiveProduct k) :
    PrincipalRegularChart (projectiveProduct k) (graphIdeal p) :=
  (exists_graphPrincipalChart p x).choose

theorem graphBaseChart_mem (p : ℕ) (x : projectiveProduct k) :
    x ∈ (graphBaseChart (k := k) p x).openSet.1 :=
  (exists_graphPrincipalChart p x).choose_spec

/-- The corresponding regular equation chart of `graphZeroDivisor p`. -/
def graphChartAt (p : ℕ) (x : projectiveProduct k) :
    RegularCartierEquationChart (projectiveContactStage (k := k) 0) (graphZeroDivisor p) :=
  cartierDivisorOfIdeal_regularChart _ (graphIdeal p) (graphIdeal_locallyPrincipalRegular p)
    (graphBaseChart p x)

theorem graphChartAt_openSet (p : ℕ) (x : projectiveProduct k) :
    (graphChartAt (k := k) p x).chart.openSet = (graphBaseChart (k := k) p x).openSet.1 := rfl

theorem graphChartAt_coefficient (p : ℕ) (x : projectiveProduct k) :
    (graphChartAt (k := k) p x).coefficient = (graphBaseChart (k := k) p x).generator := rfl

/-! ### Stage `0` -/

/-- On stage `0` the blowdown is the identity, so the total transform of the graph is the graph. -/
theorem graph_zero_case (p : ℕ) : totalGraphIdeal (k := k) 0 p = graphIdeal p := by
  apply IdealSheafData.ext_of_affine_cover _ _
    (fun y : projectiveProduct k =>
      between (projectiveProductInitial (k := k)) (Nat.zero_le 0) ⁻¹ᵁ
        (graphChartAt p y).chart.openSet)
    (fun x => ⟨(between (projectiveProductInitial (k := k)) (Nat.zero_le 0)).base x,
      graphBaseChart_mem p _⟩)
  intro y W hW
  refine IdealSheafData.ideal_eq_of_nonempty _ _ W (fun hne => ?_)
  have hWc : W.1 ≤ (graphBaseChart (k := k) p y).openSet.1 := by
    intro z hz
    have hz' := hW hz
    rwa [between_refl (projectiveProductInitial (k := k)) 0] at hz'
  have hgen : (between (projectiveProductInitial (k := k)) (Nat.zero_le 0)).appLE
      (graphChartAt p y).chart.openSet W.1 hW (graphChartAt p y).coefficient =
      ((projectiveContactStage (k := k) 0).presheaf.map (homOfLE hWc).op).hom
        (graphBaseChart (k := k) p y).generator := by
    rw [appLE_congr_hom (between_refl (projectiveProductInitial (k := k)) 0), Scheme.Hom.appLE,
      Scheme.id_app, Category.id_comp]
    rfl
  rw [totalGraphIdeal_ideal 0 p (graphChartAt p y) W hW,
    (graphBaseChart (k := k) p y).restrict_span_eq W hWc]
  exact congrArg (fun s => Ideal.span {s}) hgen

/-! ### The cover of stage `n+1` -/

/-- The cover of stage `n+1`: the selected chart open, the second Rees open, and the pieces of the
centre complement lying over the chosen graph charts of the base. -/
def graphCoverOpen (n p : ℕ) :
    Bool ⊕ (projectiveProduct k) → (projectiveContactStage (k := k) (n + 1)).Opens :=
  Sum.elim (fun b => bif b then (firstAffineOpen (n + 1)).1 else (secondAffineOpen n).1)
    (fun y => nextPuncture n ⊓
      between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ
        (graphChartAt p y).chart.openSet)

theorem graphCoverOpen_covers (n p : ℕ) (x : projectiveContactStage (k := k) (n + 1)) :
    ∃ i, x ∈ graphCoverOpen n p i := by
  rcases strictProductStage_cover n x with h | h | h
  · exact ⟨Sum.inl true, h⟩
  · exact ⟨Sum.inl false, h⟩
  · exact ⟨Sum.inr ((between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).base x),
      h, graphBaseChart_mem p _⟩

/-! ### The identity of ideal sheaves -/

set_option maxHeartbeats 4000000 in
/-- **The identity of ideal sheaves** `π^*Γ = B̃ · Π_{j<n} C_j^{j+1} · P^n` on every stage. -/
theorem totalGraphIdeal_eq : ∀ n m : ℕ, totalGraphIdeal (k := k) n (m + n) = graphTowerRHS n m
  | 0, m =>
      (graph_zero_case (m + 0)).trans
        (show graphIdeal (k := k) (m + 0) = graphTowerRHS 0 m from
          graph_ker_eq_strictTransformIdeal_zero (m + 0))
  | n + 1, m => by
      apply IdealSheafData.ext_of_affine_cover _ _ (graphCoverOpen n (m + (n + 1)))
        (graphCoverOpen_covers n (m + (n + 1)))
      rintro (b | y) W hW
      · cases b
        · exact graph_second_case n m W hW
        · exact graph_first_case n m W hW
      · have ih := totalGraphIdeal_eq n (m + 1)
        rw [show (m + 1) + n = m + (n + 1) from by omega] at ih
        exact graph_puncture_case n m (graphChartAt (m + (n + 1)) y) ih W hW

theorem totalGraphIdeal_locallyPrincipalRegular (N m : ℕ) :
    IdealLocallyPrincipalRegular (totalGraphIdeal (k := k) (N + 1) (m + (N + 1))) := by
  rw [totalGraphIdeal_eq]
  exact idealSheafDataMul_locallyPrincipalRegular
    (idealSheafDataMul_locallyPrincipalRegular
      (strictTransformIdeal_locallyPrincipalRegular (N + 1) m)
      (idealSheafDataFinProd_locallyPrincipalRegular _
        (fun j => idealSheafDataPow_locallyPrincipalRegular
          (oldIdealAt_locallyPrincipalRegular _ _) _) _))
    (idealSheafDataPow_locallyPrincipalRegular (stepExceptionalIdeal_locallyPrincipalRegular _) _)

/-! ### The Cartier-level identity -/

set_option maxHeartbeats 4000000 in
/-- **The Cartier-level identity** on stage `N+1`: `π^*Γ = B̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P`. -/
theorem totalGraphDivisor_eq (N m : ℕ) :
    totalGraphDivisor (k := k) (N + 1) (m + (N + 1)) =
      graphStrictDivisor (N + 1) m +
        ∑ j : Fin N, (j.val + 1) • oldFinalDivisor (N + 1) j.val (by omega) +
        (N + 1) • stepExceptionalDivisor N := by
  have hI := totalGraphIdeal_locallyPrincipalRegular (k := k) N m
  have h := cartierDivisorOfIdeal_tower _ (totalGraphIdeal (N + 1) (m + (N + 1)))
    (strictTransformIdeal (N + 1) (m + (N + 1))) (stepExceptionalIdeal N) (oldIdealAt (N + 1))
    N (N + 1) hI (strictTransformIdeal_locallyPrincipalRegular (N + 1) m)
    (stepExceptionalIdeal_locallyPrincipalRegular N) (oldIdealAt_locallyPrincipalRegular (N + 1))
    (totalGraphIdeal_eq (N + 1) m)
  rw [← eq_cartierDivisorOfIdeal _ _ hI (totalGraphDivisor (N + 1) (m + (N + 1)))
    (totalGraphDivisor_hasRegularEquations (N + 1) (m + (N + 1))) rfl] at h
  rw [h, graphStrictDivisor, stepExceptionalDivisor]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [oldFinalDivisor]
  congr 1
  exact cartierDivisorOfIdeal_congr _ _ _ (oldIdealAt_of_le (N + 1) j.val (by omega)) _

end KltDP.Examples.FrobeniusTowerGraphIdentity
