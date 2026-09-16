import Mathlib.Tactic

/-!
# Support obligation U-HIGHER-RESOLUTIONS: below-one coefficients persist under point blowups

Manuscript `source/manuscript.tex` lines 549–558 (the SNC sub-klt criterion used in
Proposition 2.4 and Theorem 4.5). Plan contract (`U-HIGHER-RESOLUTIONS`): "Every divisor
over the contracted normal surface is detected on a common smooth resolution
dominating the displayed SNC pair; below-one coefficients persist under every point
blowup." F11: "for a smooth surface `T` and a rational SNC boundary `B` with EVERY
coefficient `< 1` (negative coefficients allowed), `(T, B)` is sub-klt."

The coefficient arithmetic of one point blowup of an SNC pair is recorded here. If
`K_{T'} + B' = σ*(K_T + B)` with `B'` the total transform corrected by the exceptional
curve, the coefficient of the new exceptional curve is `a + b - 1` at a node of
components with coefficients `a, b`, `a - 1` at a smooth point of a single component
with coefficient `a`, and `-1` at a point outside the boundary; the old coefficients
are unchanged. Hence the predicate "every coefficient is `< 1`" is preserved, and so is
"every coefficient is `≤ 1`" (and every exceptional coefficient produced from
coefficients `< 1` is itself `< 1`, in particular it may be negative). By induction the
invariant holds after any finite sequence of point blowups, which is the arithmetic
half of the all-characteristic discrepancy comparison.

Not proved here: the actual blowup morphisms, the pullback formula
`K_{T'} = σ*K_T + E`, the SNC property of the new boundary, and that every divisor
over the surface appears on some such tower (F09, F10, F11).
-/

namespace KltDP.Support

/-- The three kinds of centers of a point blowup relative to an SNC boundary and the
resulting exceptional coefficient. -/
inductive BlowupCenter (𝕜 : Type*)
  | node (a b : 𝕜)
  | smooth (a : 𝕜)
  | outside

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Exceptional coefficient after one blowup: `a + b - 1`, `a - 1`, or `-1`. -/
def exceptionalCoefficient : BlowupCenter 𝕜 → 𝕜
  | .node a b => a + b - 1
  | .smooth a => a - 1
  | .outside => -1

/-- The boundary coefficients present at the center. -/
def BlowupCenter.coefficients : BlowupCenter 𝕜 → List 𝕜
  | .node a b => [a, b]
  | .smooth a => [a]
  | .outside => []

/-- **Below-one coefficients persist.** If every coefficient at the center is `< 1`, the
exceptional coefficient is `< 1`. -/
theorem exceptionalCoefficient_lt_one (c : BlowupCenter 𝕜)
    (h : ∀ x ∈ c.coefficients, x < 1) : exceptionalCoefficient c < 1 := by
  cases c with
  | node a b =>
    have ha := h a (by simp [BlowupCenter.coefficients])
    have hb := h b (by simp [BlowupCenter.coefficients])
    simp only [exceptionalCoefficient]
    linarith
  | smooth a =>
    have ha := h a (by simp [BlowupCenter.coefficients])
    simp only [exceptionalCoefficient]
    linarith
  | outside => simp [exceptionalCoefficient]

/-- At-most-one coefficients persist as well. -/
theorem exceptionalCoefficient_le_one (c : BlowupCenter 𝕜)
    (h : ∀ x ∈ c.coefficients, x ≤ 1) : exceptionalCoefficient c ≤ 1 := by
  cases c with
  | node a b =>
    have ha := h a (by simp [BlowupCenter.coefficients])
    have hb := h b (by simp [BlowupCenter.coefficients])
    simp only [exceptionalCoefficient]
    linarith
  | smooth a =>
    have ha := h a (by simp [BlowupCenter.coefficients])
    simp only [exceptionalCoefficient]
    linarith
  | outside => simp [exceptionalCoefficient]

/-- The exceptional coefficient is strictly below the smaller center coefficient at a
node with nonnegative coefficients (so nonnegative boundaries can produce negative
exceptional coefficients, which the criterion must allow). -/
theorem exceptionalCoefficient_node_lt (a b : 𝕜) (hb : b < 1) :
    exceptionalCoefficient (BlowupCenter.node a b) < a := by
  simp only [exceptionalCoefficient]
  linarith

/-- A boundary coefficient list stays below one after appending the exceptional coefficient. -/
theorem coefficients_lt_one_after_blowup (l : List 𝕜) (hl : ∀ x ∈ l, x < 1)
    (c : BlowupCenter 𝕜) (hc : ∀ x ∈ c.coefficients, x < 1) :
    ∀ x ∈ exceptionalCoefficient c :: l, x < 1 := by
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact exceptionalCoefficient_lt_one c hc
  · exact hl x hx

/-- **Induction along a tower of point blowups.** Starting from coefficients all `< 1` and
blowing up any finite sequence of centers whose coefficients are drawn from the current
list, every coefficient stays `< 1`. -/
theorem tower_coefficients_lt_one :
    ∀ (centers : List (BlowupCenter 𝕜)) (l : List 𝕜), (∀ x ∈ l, x < 1) →
      (∀ c ∈ centers, ∀ x ∈ c.coefficients, x < 1) →
      ∀ x ∈ centers.foldl (fun acc c => exceptionalCoefficient c :: acc) l, x < 1 := by
  intro centers
  induction centers with
  | nil => intro l hl _ x hx; exact hl x hx
  | cons c rest ih =>
    intro l hl hcs
    simp only [List.foldl_cons]
    exact ih _ (coefficients_lt_one_after_blowup l hl c (hcs c (by simp)))
      (fun c' hc' => hcs c' (by simp [hc']))

/-- **U-HIGHER-RESOLUTIONS**, arithmetic clause. -/
theorem u_higher_resolutions :
    (∀ c : BlowupCenter 𝕜, (∀ x ∈ c.coefficients, x < 1) → exceptionalCoefficient c < 1) ∧
    (∀ c : BlowupCenter 𝕜, (∀ x ∈ c.coefficients, x ≤ 1) → exceptionalCoefficient c ≤ 1) ∧
    (∀ (centers : List (BlowupCenter 𝕜)) (l : List 𝕜), (∀ x ∈ l, x < 1) →
      (∀ c ∈ centers, ∀ x ∈ c.coefficients, x < 1) →
      ∀ x ∈ centers.foldl (fun acc c => exceptionalCoefficient c :: acc) l, x < 1) :=
  ⟨exceptionalCoefficient_lt_one, exceptionalCoefficient_le_one, tower_coefficients_lt_one⟩

end KltDP.Support
