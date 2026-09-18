import KltDP.Manuscript.S04.IsolatedNodeExchange
import KltDP.Geometry.ContractionCanonicalSquare
import KltDP.Geometry.ContractionNumericalRank
import KltDP.Geometry.BirationalCartierIntersectionPullback
import KltDP.Geometry.ActualExceptionalPullback
import KltDP.Geometry.ContractionCartierKernel
import KltDP.Geometry.CanonicalWeilOfCartier
import KltDP.Geometry.PrimeCurveIntersectionFinite
import KltDP.Geometry.BlowupExceptionalCurve
import KltDP.Geometry.PointBlowupExceptionalPrimeStalk
import KltDP.Geometry.PointBlowupCenterIrreducible
import KltDP.Geometry.PointBlowupContraction
import KltDP.Geometry.SurfacePointBlowupSequenceBirational
import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.SchemePointBlowupSourceRegular

/-!
# Manuscript Theorem 4.6, terminal case `d = 1` (lines 1141–1145 and 1194–1219)

See the module docstring of `IsolatedNodeExchange` for the configuration (`Config`): an isolated
exceptional `(-2)`-curve `W`, a vertex `B` of weight three, an exterior `(-1)`-curve `P` meeting `W`
and `B` once each and nothing else. Here `B` has valency one, with unique neighbour `C` (`TConfig`).

The manuscript blows up the node `B_T ∩ C_T` of `T`; performed on `S` itself this is the point
blowup `σ : S' → S` at the node `x = B ∩ C`. On `S'` the retained family is
`{P', W', B'} ∪ (D − W − B)'` (all strict transforms, `famT`), with coefficients `−2, −1, 0` and
`λ† = λ₀ + ε u` on `Δ − B` (unchanged elsewhere, `lamTm`); the new curve `E` is exterior, of degree
`ε = 1 − λ†_C` on the new anticanonical class.

## What is proved

* **Part A (`S`-side numerics, unconditional).** The transformed matrix `A + m mᵀ` with `m = e_B + e_C`
  (`Aterm`), the degrees `q + m` (`qterm`), the null equations `A' μ = q'` (`Aterm_mulVec_lamTm`,
  from `terminal_rankOne_identity`), and the square gain `μᵀq' − 1 − λᵀq =
  2(2η(1−η) + 2h − 1)/(4h − 1) > 0` (`terminal_gain_eq`, eq:isolated-mixed-terminal-gain).
* **Part B (on the blowup).** Given the point blowup `σ : S' → S` at `x = B ∩ C` as a contraction
  of a `(-1)`-curve `E` (`IsContraction`, the union's own notion) with strict transforms
  (`ContractionLifts`): the multiplicities `m_B = m_C = 1`, `m = 0` on the other retained curves
  (`mult_B_C`, `mult_of_ne`, `mult_P`); the intersection matrix and canonical degrees of the
  retained family (`negIntersectionMatrix_famT`, `canonicalDegreeVector_famT`); the null equations
  (`null_equations`); `H₁² = L² + gain > 0` (`Lsq_lt_LsqT`); `H₁ · E = ε > 0` (`degree_LnumT_E`);
  `H₁ · Q̃ = L·Q + Σ (λ_i − μ_i)(Q·D_i) + 2 Q·P − m_Q ε` (`degree_LnumT_lift`), hence `H₁` is nef with
  null locus exactly the retained family (`degree_LnumT_nonneg`, `degree_LnumT_eq_zero_iff`); the
  family is an SNC forest of `ρ(S') − 1` rational curves (`famT_acyclic`, `pair_famT_le_one`,
  `card_famT`); Theorem 2.6 contracts it to a rank-one klt del Pezzo surface `X₁`
  (`anticanonicalContraction_terminal`); the singular points of `X₁` are exactly the image points
  and `#Sing(X₁) = #Sing(X)` (`singularPoints_eq_imagePoints_T`, `card_components_famT`); the
  minimal resolution of `X₁` has `ρ ≤ ρ(S) − 1`, since `P'` and then the image of `W'` are
  exceptional `(-1)`-curves (`exists_terminal_datum`).
* **Interface.** `isolatedExchangeTerminalHyp_of_blowups` / `isolatedExchangeHyp_of_blowups`
  (Theorem 4.6 as consumed by Theorem 7.1) from the two inputs below, and
  `isolatedExchangeHyp_of_literal` with input (ii) replaced by the union's Stacks 0AGQ literal.

## The two isolated geometric inputs (standard blowup geometry, not manuscript theorems)

* (i) `HasContractionLifts k`: strict transforms along a contraction of a `(-1)`-curve
  (Hartshorne II.7.15, V.3.6: `b^*Q = Q̃ + m_z(Q) E`, `b(Q̃) = Q`, every curve of the source other
  than `E` is a strict transform, `m = 0` iff `z ∉ Q`, `Q̃ ≅ Q` when `m ≤ 1`). The union records the
  multiplicity identification as unbuilt (`Geometry/PointBlowupPullbackWeil`).
* (ii) `HasPointBlowups k`: the blowup of a regular projective surface at a closed point exists and
  its exceptional curve is a `(-1)`-curve. **Discharged from the union's Stacks 0AGQ literal**
  `KltDP.Literature.Stacks.BlowupRegularPointLiteral k` (`hasPointBlowups_of_literal`).

Nothing here uses a new axiom; all `#print axioms` lists consist of union literals.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S04.Replacement

universe u

namespace KltDP.Manuscript.S04

/-! ### Sums over `α ⊕ Unit` -/

theorem mulVec_sum_apply' {α : Type*} [Fintype α] (N : Matrix (α ⊕ Unit) (α ⊕ Unit) ℚ)
    (x : α ⊕ Unit → ℚ) (a : α ⊕ Unit) :
    (N *ᵥ x) a = ∑ j : α, N a (Sum.inl j) * x (Sum.inl j) + N a (Sum.inr ()) * x (Sum.inr ()) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sum_type, Fintype.sum_unique (fun u : Unit => N a (Sum.inr u) * x (Sum.inr u))]

theorem dot_sum' {α : Type*} [Fintype α] (x y : α ⊕ Unit → ℚ) :
    x ⬝ᵥ y = ∑ j : α, x (Sum.inl j) * y (Sum.inl j) + x (Sum.inr ()) * y (Sum.inr ()) := by
  unfold dotProduct
  rw [Fintype.sum_sum_type, Fintype.sum_unique (fun u : Unit => x (Sum.inr u) * y (Sum.inr u))]

/-! ## Part B (statement): strict transforms along a contraction

A contraction `b : S → T` of a `(-1)`-curve `E` is, in the union, literally the point blowup of `T`
at the centre `z = b(E)` (`IsContraction` contains `IsPointBlowupAt`). The following structure
records the standard consequences (Hartshorne II.7.15, V.3.1–V.3.6): every prime curve `Q` of `T`
has a strict transform `Q̃ = lift Q` with `b(Q̃) = Q`, every prime curve of `S` other than `E` is a
strict transform, `b^*Q = Q̃ + m E` with `m = m_z(Q) ≥ 0`, `m = 0` iff `z ∉ Q`, and `Q̃ ≅ Q` when
`Q` is regular at `z` (`m ≤ 1`). -/

/-- Strict transforms along the contraction `b` of `E` (Hartshorne V.3.6). -/
structure ContractionLifts {k : Type u} [Field k] [IsAlgClosed k]
    {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme} {E : S.PrimeCurve}
    (hb : IsContraction S T b E) (hS : ∀ s : S.Point, RegularPoint S.toScheme s) where
  /-- The strict transform. -/
  lift : T.PrimeCurve → S.PrimeCurve
  /-- The multiplicity of `Q` at the centre. -/
  mult : T.PrimeCurve → ℕ
  image_lift : ∀ Q : T.PrimeCurve, b.base '' (lift Q : Set S.toScheme) = (Q : Set T.toScheme)
  lift_surj : ∀ Q' : S.PrimeCurve, Q' ≠ E → ∃ Q : T.PrimeCurve, lift Q = Q'
  pullback_eq : ∀ Q : T.PrimeCurve,
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    DominantCartierPullback.pullbackHom b (T.primeCurveCartier hb.regular Q) =
      S.primeCurveCartier hS (lift Q) + (mult Q : ℤ) • S.primeCurveCartier hS E
  mult_eq_zero : ∀ Q : T.PrimeCurve,
    Disjoint (Q : Set T.toScheme) (b.base '' (E : Set S.toScheme)) → mult Q = 0
  mult_pos : ∀ Q : T.PrimeCurve,
    ((Q : Set T.toScheme) ∩ b.base '' (E : Set S.toScheme)).Nonempty → 0 < mult Q
  lift_iso : ∀ Q : T.PrimeCurve, mult Q ≤ 1 →
    ∃ e : (lift Q).toScheme ≅ Q.toScheme, e.hom ≫ Q.toSpec = (lift Q).toSpec

/-- **Isolated geometric input (i)**: every contraction of a `(-1)`-curve between regular
projective surfaces admits strict transforms (Hartshorne V.3.6; the strict-transform multiplicity
identification is recorded as unbuilt in the union, `Geometry/PointBlowupPullbackWeil`). -/
def HasContractionLifts (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∀ {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme} {E : S.PrimeCurve}
    (hb : IsContraction S T b E) (hS : ∀ s : S.Point, RegularPoint S.toScheme s),
    IsMinusOneCurve hS E → Nonempty (ContractionLifts hb hS)

/-- **Isolated geometric input (ii)**: the point blowup of a regular projective surface at a closed
point exists and its exceptional curve is a `(-1)`-curve (Hartshorne V.3.1, Stacks 0AGQ/0AGR/0C5P),
phrased as a contraction with centre `x`. -/
def HasPointBlowups (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∀ (T : NormalProjectiveSurface k), (∀ t : T.Point, RegularPoint T.toScheme t) →
    ∀ x : T.Point, IsClosed ({x} : Set T.toScheme) →
    ∃ (S : NormalProjectiveSurface k) (σ : S.toScheme ⟶ T.toScheme) (E : S.PrimeCurve)
      (hS : ∀ s : S.Point, RegularPoint S.toScheme s),
      IsContraction S T σ E ∧ IsMinusOneCurve hS E ∧ σ.base '' (E : Set S.toScheme) = {x}

namespace ContractionLifts

section General

variable {k : Type u} [Field k] [IsAlgClosed k] {S T : NormalProjectiveSurface k}
  {b : S.toScheme ⟶ T.toScheme} {E : S.PrimeCurve} (hb : IsContraction S T b E)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)

include hb in
theorem E_exceptional : IsExceptionalCurve b E := (hb.isExceptionalCurve_iff_eq E).mpr rfl

/-- `b^*D · b^*D' = D · D'`. -/
theorem pair_pullback_pullback (D D' : CartierDivisor T.toScheme) :
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    (S.intersectionPairing hS (DominantCartierPullback.pullbackHom b D)
      (DominantCartierPullback.pullbackHom b D') : ℚ) =
      (T.intersectionPairing hb.regular D D' : ℚ) := by
  letI : IsProper b := hb.isProper
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  exact_mod_cast BirationalCartierIntersectionPullback.intersectionPairing_pullback b hb.over_base
    ((isBirational_iff_isBirationalScheme b).mp hb.birational) hS hb.regular D D'

/-- `b^*D · E = 0`. -/
theorem pair_pullback_E (D : CartierDivisor T.toScheme) :
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    (S.intersectionPairing hS (DominantCartierPullback.pullbackHom b D)
      (S.primeCurveCartier hS E) : ℚ) = 0 := by
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  rw [S.intersectionPairing_primeCurve hS]
  exact_mod_cast (E_exceptional hb).intersectionNumber_pullback_eq_zero b hb.over_base E D

theorem pair_E_pullback (D : CartierDivisor T.toScheme) :
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    (S.intersectionPairing hS (S.primeCurveCartier hS E)
      (DominantCartierPullback.pullbackHom b D) : ℚ) = 0 := by
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  rw [S.intersectionPairing_symm hS]
  exact pair_pullback_E hb hS D

/-- `E · E = -1`. -/
theorem pair_E_E (hE : IsMinusOneCurve hS E) :
    (S.intersectionPairing hS (S.primeCurveCartier hS E) (S.primeCurveCartier hS E) : ℚ) = -1 := by
  rw [S.intersectionPairing_primeCurve hS]
  have h : E.intersectionNumber (S.primeCurveCartier hS E) = -1 := hE.selfIntersection
  rw [h]
  norm_num

theorem cartierClass_add (D D' : CartierDivisor S.toScheme) :
    NefNullCurveNegativeSquare.cartierClass S (D + D') =
      NefNullCurveNegativeSquare.cartierClass S D + NefNullCurveNegativeSquare.cartierClass S D' := by
  simp only [NefNullCurveNegativeSquare.cartierClass, map_add]

theorem cartierClass_nsmul (n : ℕ) (D : CartierDivisor S.toScheme) :
    NefNullCurveNegativeSquare.cartierClass S ((n : ℤ) • D) =
      (n : ℚ) • NefNullCurveNegativeSquare.cartierClass S D := by
  simp only [NefNullCurveNegativeSquare.cartierClass, map_zsmul]
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]

/-- A compatible canonical divisor of the source: `K_S = b^*K_T + E`. -/
theorem exists_canonical (hE : IsMinusOneCurve hS E) (KT : CartierDivisor T.toScheme)
    (eKT : cartierDivisorModule T.toScheme KT ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior T.structureMorphism 2) :
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    ∃ K : CartierDivisor S.toScheme,
      Nonempty (cartierDivisorModule S.toScheme K ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2) ∧
      K = DominantCartierPullback.pullbackHom b KT + S.primeCurveCartier hS E := by
  letI : IsProper b := hb.isProper
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hS
  letI : IsSmoothOfRelativeDimension 2 T.structureMorphism :=
    T.isSmoothOfRelativeDimension_two_of_regularPoints hb.regular
  have hbir := (isBirational_iff_isBirationalScheme b).mp hb.birational
  obtain ⟨K, ⟨eK⟩, hpush⟩ := IsCanonicalWeilDivisor.exists_compatible_canonical_cartier S T b
    hb.over_base hbir (T.cartierToWeilHom KT) (IsCanonicalWeilDivisor.of_cartier T KT eKT)
  exact ⟨K, ⟨eK⟩, hb.compatible_canonical_difference hS hE KT K eK hpush⟩

end General

section Lifts

variable {k : Type u} [Field k] [IsAlgClosed k] {S T : NormalProjectiveSurface k}
  {b : S.toScheme ⟶ T.toScheme} {E : S.PrimeCurve} {hb : IsContraction S T b E}
  {hS : ∀ s : S.Point, RegularPoint S.toScheme s} (L : ContractionLifts hb hS)
  (hE : IsMinusOneCurve hS E)

/-- The numerical class of the strict transform: `[Q̃] = b^*[Q] − m [E]`. -/
theorem cartierClass_lift (Q : T.PrimeCurve) :
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    NefNullCurveNegativeSquare.cartierClass S (S.primeCurveCartier hS (L.lift Q)) =
      NefNullCurveNegativeSquare.cartierClass S
        (DominantCartierPullback.pullbackHom b (T.primeCurveCartier hb.regular Q)) -
      (L.mult Q : ℚ) • NefNullCurveNegativeSquare.cartierClass S (S.primeCurveCartier hS E) := by
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  rw [L.pullback_eq Q, cartierClass_add, cartierClass_nsmul, add_sub_cancel_right]

include hE in
/-- `Q̃₁ · Q̃₂ = Q₁ · Q₂ − m₁ m₂`. -/
theorem pair_lift_lift (Q₁ Q₂ : T.PrimeCurve) :
    (S.intersectionPairing hS (S.primeCurveCartier hS (L.lift Q₁))
      (S.primeCurveCartier hS (L.lift Q₂)) : ℚ) =
      (T.intersectionPairing hb.regular (T.primeCurveCartier hb.regular Q₁)
        (T.primeCurveCartier hb.regular Q₂) : ℚ) - L.mult Q₁ * L.mult Q₂ := by
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  rw [← NefNullCurveNegativeSquare.cartierClass_pairing S hS, L.cartierClass_lift Q₁,
    L.cartierClass_lift Q₂, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right, LinearMap.BilinForm.smul_right]
  simp only [NefNullCurveNegativeSquare.cartierClass_pairing S hS, smul_eq_mul]
  rw [pair_pullback_pullback hb hS, pair_pullback_E hb hS, pair_E_pullback hb hS, pair_E_E hS hE]
  ring

include hE in
/-- `Q̃ · E = m`. -/
theorem pair_lift_E (Q : T.PrimeCurve) :
    (S.intersectionPairing hS (S.primeCurveCartier hS (L.lift Q)) (S.primeCurveCartier hS E) : ℚ) =
      L.mult Q := by
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  rw [← NefNullCurveNegativeSquare.cartierClass_pairing S hS, L.cartierClass_lift Q,
    LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]
  simp only [NefNullCurveNegativeSquare.cartierClass_pairing S hS, smul_eq_mul]
  rw [pair_pullback_E hb hS, pair_E_E hS hE]
  ring

include hE in
theorem pair_E_lift (Q : T.PrimeCurve) :
    (S.intersectionPairing hS (S.primeCurveCartier hS E) (S.primeCurveCartier hS (L.lift Q)) : ℚ) =
      L.mult Q := by
  rw [S.intersectionPairing_symm hS]
  exact L.pair_lift_E hE Q

/-- The strict transform is never the exceptional curve. -/
theorem lift_ne_E (Q : T.PrimeCurve) : L.lift Q ≠ E := by
  intro h
  obtain ⟨z, -, hz, -, -⟩ := hb.center
  have himg := L.image_lift Q
  rw [h, hz] at himg
  haveI : Subsingleton (Q : Set T.toScheme) := (himg ▸ Set.subsingleton_singleton).coe_sort
  have hle := topologicalKrullDim_nonpos_of_subsingleton (Q : Set T.toScheme)
  rw [Q.dimension_one] at hle
  exact (WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)).not_le hle

theorem lift_injective : Function.Injective L.lift := by
  intro Q₁ Q₂ h
  apply PrimeCurve.ext
  rw [← L.image_lift Q₁, ← L.image_lift Q₂, h]

include hE in
/-- Two curves through the centre meeting once are both regular there: `m₁ = m₂ = 1`. -/
theorem mult_eq_one_of_pair_one {Q₁ Q₂ : T.PrimeCurve} (hne : Q₁ ≠ Q₂)
    (hpair : T.intersectionPairing hb.regular (T.primeCurveCartier hb.regular Q₁)
      (T.primeCurveCartier hb.regular Q₂) = 1)
    (h₁ : 0 < L.mult Q₁) (h₂ : 0 < L.mult Q₂) : L.mult Q₁ = 1 ∧ L.mult Q₂ = 1 := by
  have hnn : (0 : ℤ) ≤ S.intersectionPairing hS (S.primeCurveCartier hS (L.lift Q₁))
      (S.primeCurveCartier hS (L.lift Q₂)) :=
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg S hS _ _
      (fun h => hne (L.lift_injective h))
  have h := L.pair_lift_lift hE Q₁ Q₂
  rw [hpair] at h
  have hq : (L.mult Q₁ : ℚ) * L.mult Q₂ ≤ 1 := by
    have : (0 : ℚ) ≤ (S.intersectionPairing hS (S.primeCurveCartier hS (L.lift Q₁))
        (S.primeCurveCartier hS (L.lift Q₂)) : ℚ) := by exact_mod_cast hnn
    push_cast at h
    linarith
  have hm : L.mult Q₁ * L.mult Q₂ ≤ 1 := by exact_mod_cast hq
  have h1 : L.mult Q₁ * L.mult Q₂ = 1 := le_antisymm hm (Nat.mul_pos h₁ h₂)
  exact ⟨Nat.eq_one_of_mul_eq_one_right h1, Nat.eq_one_of_mul_eq_one_left h1⟩

/-- Rationality passes to strict transforms of curves regular at the centre. -/
theorem lift_rational (Q : T.PrimeCurve) (hm : L.mult Q ≤ 1)
    (hQ : ∃ e : Q.toScheme ≅ projectiveSpace k 1, e.hom ≫ projectiveSpaceToSpec k 1 = Q.toSpec) :
    ∃ e : (L.lift Q).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (L.lift Q).toSpec := by
  obtain ⟨e₁, he₁⟩ := L.lift_iso Q hm
  obtain ⟨e₂, he₂⟩ := hQ
  exact ⟨e₁ ≪≫ e₂, by rw [Iso.trans_hom, Category.assoc, he₂, he₁]⟩

include hE in
/-- The strict transform of a `(-1)`-curve missing the centre is a `(-1)`-curve. -/
theorem lift_minusOne (Q : T.PrimeCurve) (hQ : IsMinusOneCurve hb.regular Q)
    (hm : L.mult Q = 0) : IsMinusOneCurve hS (L.lift Q) := by
  refine ⟨L.lift_rational Q (by omega) hQ.isoProjectiveLine, ?_⟩
  have h := L.pair_lift_lift hE Q Q
  rw [hm, S.intersectionPairing_primeCurve hS, T.intersectionPairing_primeCurve hb.regular] at h
  have hQ2 : Q.intersectionNumber (T.primeCurveCartier hb.regular Q) = -1 := hQ.selfIntersection
  rw [hQ2] at h
  push_cast at h
  have h' : ((L.lift Q).intersectionNumber (S.primeCurveCartier hS (L.lift Q)) : ℚ) = -1 := by
    linarith
  exact_mod_cast h'

include hE in
/-- `K_S · Q̃ = K_T · Q + m` for `K_S = b^*K_T + E`. -/
theorem intersectionNumber_lift_canonical (KT : CartierDivisor T.toScheme)
    (K : CartierDivisor S.toScheme) :
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    K = DominantCartierPullback.pullbackHom b KT + S.primeCurveCartier hS E →
    ∀ Q : T.PrimeCurve,
      ((L.lift Q).intersectionNumber K : ℚ) = (Q.intersectionNumber KT : ℚ) + L.mult Q := by
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  intro hK Q
  rw [← S.intersectionPairing_primeCurve hS, ← T.intersectionPairing_primeCurve hb.regular,
    ← NefNullCurveNegativeSquare.cartierClass_pairing S hS, hK, cartierClass_add,
    L.cartierClass_lift Q, LinearMap.BilinForm.add_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, LinearMap.BilinForm.smul_right]
  simp only [NefNullCurveNegativeSquare.cartierClass_pairing S hS, smul_eq_mul]
  rw [pair_pullback_pullback hb hS, pair_pullback_E hb hS, pair_E_pullback hb hS, pair_E_E hS hE]
  ring

include hE in
/-- `K_S · E = -1` for `K_S = b^*K_T + E`. -/
theorem intersectionNumber_E_canonical (KT : CartierDivisor T.toScheme)
    (K : CartierDivisor S.toScheme) :
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    K = DominantCartierPullback.pullbackHom b KT + S.primeCurveCartier hS E →
    (E.intersectionNumber K : ℚ) = -1 := by
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  intro hK
  rw [← S.intersectionPairing_primeCurve hS, hK, S.intersectionPairing_add_left hS]
  push_cast
  have h1 := pair_pullback_E hb hS KT
  have h2 := pair_E_E hS hE
  linarith

end Lifts

end ContractionLifts

/-! ## Graph theory: a graph on `V ⊕ Unit` whose edges are edges of a forest on `V` -/

section InlEdges

open SimpleGraph

/-- Every vertex of a nontrivial walk lies on one of its edges. -/
theorem mem_edge_of_mem_support_cons {V : Type*} {G : SimpleGraph V} {u a v : V}
    (h : G.Adj u a) (q : G.Walk a v) (w : V) (hw : w ∈ (Walk.cons h q).support) :
    ∃ e ∈ (Walk.cons h q).edges, w ∈ e := by
  induction q generalizing u with
  | nil =>
    rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hw
    refine ⟨_, by rw [Walk.edges_cons]; exact List.mem_cons.mpr (Or.inl rfl), ?_⟩
    rcases hw with h1 | h1
    · rw [h1]
      exact Sym2.mem_mk_left _ _
    · rw [h1]
      exact Sym2.mem_mk_right _ _
  | @cons a b v h' q ih =>
    rw [Walk.support_cons, List.mem_cons] at hw
    rcases hw with h1 | hw
    · refine ⟨_, by rw [Walk.edges_cons]; exact List.mem_cons.mpr (Or.inl rfl), ?_⟩
      rw [h1]
      exact Sym2.mem_mk_left _ _
    · obtain ⟨e, he, hwe⟩ := ih h' hw
      exact ⟨e, by rw [Walk.edges_cons]; exact List.mem_cons_of_mem _ he, hwe⟩

/-- A graph on `V ⊕ Unit` all of whose edges join `inl`-vertices adjacent in an acyclic graph
`G` on `V` is acyclic. -/
theorem isAcyclic_of_inl_edges {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    (G' : SimpleGraph (V ⊕ Unit))
    (hedge : ∀ a b, G'.Adj a b → ∃ i j, a = Sum.inl i ∧ b = Sum.inl j ∧ G.Adj i j) :
    G'.IsAcyclic := by
  classical
  intro u c hc
  cases c with
  | nil => exact Walk.IsCycle.not_of_nil hc
  | @cons _ a _ h q =>
    obtain ⟨i₀, -, -, -, -⟩ := hedge _ _ h
    let φ : V ⊕ Unit → V := Sum.elim id (fun _ => i₀)
    have hφ : ∀ {a b : V ⊕ Unit}, G'.Adj a b → G.Adj (φ a) (φ b) := by
      intro a b hab
      obtain ⟨i, j, rfl, rfl, hij⟩ := hedge a b hab
      exact hij
    let f : G' →g G := ⟨φ, hφ⟩
    have hsup : ∀ w ∈ (Walk.cons h q).support, ∃ i, w = Sum.inl i := by
      intro w hw
      obtain ⟨e, he, hwe⟩ := mem_edge_of_mem_support_cons h q w hw
      have hE : e ∈ G'.edgeSet := Walk.edges_subset_edgeSet _ he
      induction e using Sym2.ind with
      | h a b =>
        obtain ⟨i, j, rfl, rfl, -⟩ := hedge a b hE
        rcases Sym2.mem_iff.mp hwe with rfl | rfl
        · exact ⟨i, rfl⟩
        · exact ⟨j, rfl⟩
    have hinj : ∀ w₁ ∈ (Walk.cons h q).support, ∀ w₂ ∈ (Walk.cons h q).support,
        φ w₁ = φ w₂ → w₁ = w₂ := by
      intro w₁ h₁ w₂ h₂ heq
      obtain ⟨i, rfl⟩ := hsup w₁ h₁
      obtain ⟨j, rfl⟩ := hsup w₂ h₂
      simp only [φ, Sum.elim_inl, id] at heq
      rw [heq]
    apply hG ((Walk.cons h q).map f)
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · rw [Walk.edges_map]
      refine List.Nodup.map_on ?_ hc.isCircuit.isTrail.edges_nodup
      intro e₁ he₁ e₂ he₂ heq
      have hE₁ : e₁ ∈ G'.edgeSet := Walk.edges_subset_edgeSet _ he₁
      have hE₂ : e₂ ∈ G'.edgeSet := Walk.edges_subset_edgeSet _ he₂
      induction e₁ using Sym2.ind with
      | h a₁ b₁ =>
        induction e₂ using Sym2.ind with
        | h a₂ b₂ =>
          obtain ⟨i₁, j₁, rfl, rfl, -⟩ := hedge _ _ hE₁
          obtain ⟨i₂, j₂, rfl, rfl, -⟩ := hedge _ _ hE₂
          have hf : ∀ i : V, f (Sum.inl i) = i := fun i => rfl
          rw [Sym2.map_pair_eq, Sym2.map_pair_eq, hf, hf, hf, hf, Sym2.eq_iff] at heq
          rw [Sym2.eq_iff]
          rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
          · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
    · rw [Ne, Walk.map_eq_nil_iff]
      exact hc.ne_nil
    · rw [Walk.support_map, Walk.support_eq_cons (Walk.cons h q), List.map_cons, List.tail_cons]
      refine List.Nodup.map_on ?_ hc.support_nodup
      intro w₁ h₁ w₂ h₂ heq
      exact hinj w₁ (List.mem_of_mem_tail h₁) w₂ (List.mem_of_mem_tail h₂) heq

end InlEdges

/-! ## The divisor route to numerical classes on a regular surface -/

section WeilNumerical

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)

theorem rationalWeilNumericalMap_rationalCartier' (D : CartierDivisor X.toScheme) :
    X.rationalWeilNumericalMap hX (X.rationalCartierToWeilHom D) =
      NefNullCurveNegativeSquare.cartierClass X D := by
  have h : X.regularWeilPicardClass hX (X.cartierToWeilHom D) = cartierPicardClass X.toScheme D :=
    X.regularWeilClassPicardEquiv_of_cartier hX D
  change X.rationalWeilNumericalMap hX (rationalizeWeilDivisor X (X.cartierToWeilHom D)) = _
  rw [← X.picardNumericalMap_regularWeilPicardClass hX, h]
  rfl

theorem rationalCartierToWeilHom_primeCurveCartier' (Q : X.PrimeCurve) :
    X.rationalCartierToWeilHom (X.primeCurveCartier hX Q) = Finsupp.single Q (1 : ℚ) := by
  change rationalizeWeilDivisor X (X.cartierToWeilHom (X.primeCurveCartier hX Q)) = _
  rw [X.cartierToWeilHom_primeCurveCartier hX Q, rationalizeWeilDivisor_single, Int.cast_one]

theorem rationalWeilNumericalMap_single' (Q : X.PrimeCurve) :
    X.rationalWeilNumericalMap hX (Finsupp.single Q (1 : ℚ)) =
      DisjointNegativeCurvesRank.curveClass X hX Q := by
  rw [← rationalCartierToWeilHom_primeCurveCartier' X hX Q,
    rationalWeilNumericalMap_rationalCartier' X hX]
  rfl

include hX in
/-- Clearing denominators of a rational Weil divisor: a Cartier divisor `Hm` with `Hm = −n D`. -/
theorem exists_cartier_multiple_T (D : X.RationalWeilDivisor) :
    ∃ (n : ℕ) (Hm : CartierDivisor X.toScheme), 0 < n ∧
      X.rationalCartierToWeilHom Hm = -((n : ℚ) • D) := by
  obtain ⟨n, hn, A, hA⟩ := X.exists_positive_integral_multiple D
  refine ⟨n, (X.regularCartierWeilEquiv hX).symm (-A), hn, ?_⟩
  have h1 : X.rationalCartierToWeilHom ((X.regularCartierWeilEquiv hX).symm (-A)) =
      rationalizeWeilDivisor X (-A) := by
    change rationalizeWeilDivisor X (X.cartierToWeilHom _) = _
    rw [← X.regularCartierWeilEquiv_apply hX, AddEquiv.apply_symm_apply]
  rw [h1, map_neg, hA, Nat.cast_smul_eq_nsmul]

end WeilNumerical

/-! ## Part A: the `S`-side numerics of the terminal family -/

namespace IsolatedNodeExchange

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k) [DecidableEq R.Vertices]
  (W B : R.Vertices) (P : R.S.PrimeCurve)

section Terminal

variable [DecidableRel R.graph.Adj]

/-- Valency one gives a unique neighbour. -/
theorem exists_unique_neighbour (hd : R.graph.degree B = 1) :
    ∃ C : R.Vertices, R.graph.Adj B C ∧ ∀ j, R.graph.Adj B j → j = C := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_one] at hd
  obtain ⟨C, hC⟩ := hd
  refine ⟨C, ?_, fun j hj => ?_⟩
  · have hmem : C ∈ R.graph.neighborFinset B := by
      rw [hC]
      exact Finset.mem_singleton_self C
    exact (SimpleGraph.mem_neighborFinset _ _ _).mp hmem
  · have hmem : j ∈ R.graph.neighborFinset B := (SimpleGraph.mem_neighborFinset _ _ _).mpr hj
    rw [hC] at hmem
    exact Finset.mem_singleton.mp hmem

variable (C : R.Vertices)

/-- The terminal configuration of manuscript lines 1141–1145: `Config` with `B` of valency one and
`C` its unique neighbour. -/
structure TConfig : Prop extends Config R W B P where
  hBC : R.graph.Adj B C
  hCu : ∀ j, R.graph.Adj B j → j = C

variable {R W B P C} in
theorem TConfig.C_ne_B (tc : TConfig R W B P C) : C ≠ B := (R.graph.ne_of_adj tc.hBC).symm

variable {R W B P C} in
theorem TConfig.C_ne_W (tc : TConfig R W B P C) : C ≠ W := by
  intro h
  have h' : R.graph.Adj B W := by
    have := tc.hBC
    rwa [h] at this
  exact tc.hWiso B h'.symm

/-- `C` as a member of `D − B`. -/
abbrev Cd (tc : TConfig R W B P C) : D0 R B := ⟨C, tc.C_ne_B⟩

theorem Cd_ne_Wd (tc : TConfig R W B P C) : Cd R W B P C tc ≠ Wd R W B P tc.toConfig :=
  fun h => tc.C_ne_W (congrArg Subtype.val h)

/-- Row `B` of `A`. -/
theorem A_B_apply (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C) (j : R.Vertices) :
    R.A B j = if j = B then 3 else if j = C then -1 else 0 := by
  rw [R.A_eq_graphWeightMatrix, KltDP.LinearAlgebra.graphWeightMatrix_apply]
  by_cases hjB : B = j
  · rw [if_pos hjB, if_pos hjB.symm]
    exact w_B_eq_three R W B P p hp tc.toConfig
  · rw [if_neg hjB, if_neg (Ne.symm hjB)]
    by_cases hjC : j = C
    · have hadj : R.graph.Adj B j := by
        rw [hjC]
        exact tc.hBC
      rw [if_pos hjC, if_pos hadj]
    · rw [if_neg hjC, if_neg (fun h => hjC (tc.hCu j h))]

/-- `a = e_C` (manuscript line 1194). -/
theorem vvec_eq_single (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C) :
    vvec R B = Pi.single (Cd R W B P C tc) 1 := by
  funext i
  show -R.A B i.1 = _
  rw [A_B_apply R W B P C p hp tc i.1, if_neg i.2, Pi.single_apply]
  by_cases h : i.1 = C
  · rw [if_pos h, if_pos (Subtype.ext h)]
    norm_num
  · rw [if_neg h, if_neg (fun h' => h (congrArg Subtype.val h'))]
    norm_num

theorem vvec_dot (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C) (x : D0 R B → ℚ) :
    vvec R B ⬝ᵥ x = x (Cd R W B P C tc) := by
  rw [vvec_eq_single R W B P C p hp tc, single_dotProduct, one_mul]

theorem vvec_apply (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C) (i : D0 R B) :
    vvec R B i = if i = Cd R W B P C tc then 1 else 0 := by
  rw [vvec_eq_single R W B P C p hp tc, Pi.single_apply]

/-- `λ†_C = s + ε t`. -/
theorem lamT_Cd (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C) :
    lamT R B (Cd R W B P C tc) =
      vvec R B ⬝ᵥ theta R B + epsT R B * (vvec R B ⬝ᵥ wv R B) := by
  rw [vvec_dot R W B P C p hp tc, vvec_dot R W B P C p hp tc]
  simp only [lamT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem lamT_Wd (tc : TConfig R W B P C) : lamT R B (Wd R W B P tc.toConfig) = 0 := by
  simp only [lamT, Pi.add_apply, Pi.smul_apply, smul_eq_mul, theta_Wd R W B P tc.toConfig,
    wv_Wd R W B P tc.toConfig, mul_zero, add_zero]

/-! ### The multiplicity vector `m = e_B + e_C` -/

/-- `m = e_B + e_C`: the multiplicities of the exceptional curves at the node `x = B ∩ C`. -/
def mv : R.Vertices → ℚ := Pi.single B 1 + Pi.single C 1

theorem mv_apply (i : R.Vertices) :
    mv R B C i = (if i = B then 1 else 0) + (if i = C then 1 else 0) := by
  simp only [mv, Pi.add_apply, Pi.single_apply]

theorem mv_B (tc : TConfig R W B P C) : mv R B C B = 1 := by
  rw [mv_apply, if_pos rfl, if_neg tc.C_ne_B.symm]
  norm_num

theorem mv_C (tc : TConfig R W B P C) : mv R B C C = 1 := by
  rw [mv_apply, if_neg tc.C_ne_B, if_pos rfl]
  norm_num

theorem mv_of_ne (i : R.Vertices) (hB : i ≠ B) (hC : i ≠ C) : mv R B C i = 0 := by
  rw [mv_apply, if_neg hB, if_neg hC]
  norm_num

theorem mv_dot (x : R.Vertices → ℚ) : mv R B C ⬝ᵥ x = x B + x C := by
  simp only [mv, add_dotProduct, single_dotProduct, one_mul]

theorem mv_nonneg (i : R.Vertices) : 0 ≤ mv R B C i := by
  rw [mv_apply]
  split_ifs <;> norm_num

/-! ### The coefficient vector `(μ_V, −2)` with `μ_B = 0`, `μ_W = −1`, `μ = λ†` elsewhere -/

/-- The coefficients of the composite `S' → X₁` on the strict transforms: `0` on `B`, `−1` on `W`,
`λ†` on `D − B − W`, and `−2` on `P` (manuscript lines 1177–1178 and 1205–1207). -/
def lamTm : R.Vertices ⊕ Unit → ℚ :=
  Sum.elim (fun i => if h : i = B then 0 else lamT R B ⟨i, h⟩ - if i = W then 1 else 0)
    (fun _ => -2)

@[simp] theorem lamTm_inr (u : Unit) : lamTm R W B (Sum.inr u) = -2 := rfl

theorem lamTm_inl_B : lamTm R W B (Sum.inl B) = 0 := by
  simp [lamTm]

theorem lamTm_inl_of_ne (i : R.Vertices) (h : i ≠ B) :
    lamTm R W B (Sum.inl i) = lamT R B ⟨i, h⟩ - if i = W then 1 else 0 := by
  simp [lamTm, h]

theorem lamTm_inl_W (tc : TConfig R W B P C) : lamTm R W B (Sum.inl W) = -1 := by
  rw [lamTm_inl_of_ne R W B W tc.hWB, if_pos rfl]
  have h : lamT R B ⟨W, tc.hWB⟩ = 0 := lamT_Wd R W B P C tc
  rw [h]
  norm_num

theorem lamTm_inl_C (tc : TConfig R W B P C) :
    lamTm R W B (Sum.inl C) = lamT R B (Cd R W B P C tc) := by
  rw [lamTm_inl_of_ne R W B C tc.C_ne_B, if_neg tc.C_ne_W, sub_zero]

/-- The restriction of the coefficients to `D`, in block form: `0` at `B`, `λ† − e_W` on `D − B`. -/
theorem lamV_eq (tc : TConfig R W B P C) :
    (fun i => lamTm R W B (Sum.inl i)) =
      ext R B 0 (lamT R B - Pi.single (Wd R W B P tc.toConfig) 1) := by
  funext i
  by_cases h : i = B
  · subst h
    rw [lamTm_inl_B, ext_C]
  · rw [lamTm_inl_of_ne R W B i h, ext_apply_of_ne R B _ _ h, Pi.sub_apply, Pi.single_apply]
    congr 1
    by_cases hW : i = W
    · rw [if_pos hW, if_pos (Subtype.ext hW)]
    · rw [if_neg hW, if_neg (fun h' => hW (congrArg Subtype.val h'))]

theorem lamTm_lt_one (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C)
    (a : R.Vertices ⊕ Unit) : lamTm R W B a < 1 := by
  rcases a with i | u
  · by_cases h : i = B
    · subst h
      rw [lamTm_inl_B]
      norm_num
    · rw [lamTm_inl_of_ne R W B i h]
      have := lamT_lt_one R W B P p hp tc.toConfig ⟨i, h⟩
      split_ifs <;> linarith
  · rw [lamTm_inr]
    norm_num

theorem lamTm_inl_nonneg (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C)
    (i : R.Vertices) (hi : i ≠ W) : 0 ≤ lamTm R W B (Sum.inl i) := by
  by_cases h : i = B
  · subst h
    rw [lamTm_inl_B]
  · rw [lamTm_inl_of_ne R W B i h, if_neg hi, sub_zero]
    exact lamT_nonneg R W B P p hp tc.toConfig ⟨i, h⟩

/-! ### The transformed matrix `A + m mᵀ` and degrees `q + m` -/

/-- The negative intersection matrix of the family `{D_i'} ∪ {P'}` on `S'`, computed on `S`:
`A + m mᵀ` on `D`, contacts `−p` with `P'`, and `P'² = −1`. -/
def Aterm : Matrix (R.Vertices ⊕ Unit) (R.Vertices ⊕ Unit) ℚ :=
  Matrix.of fun a b =>
    match a, b with
    | Sum.inl i, Sum.inl j => R.A i j + mv R B C i * mv R B C j
    | Sum.inl i, Sum.inr _ => -contactVector R P i
    | Sum.inr _, Sum.inl j => -contactVector R P j
    | Sum.inr _, Sum.inr _ => 1

@[simp] theorem Aterm_inl_inl (i j : R.Vertices) :
    Aterm R B P C (Sum.inl i) (Sum.inl j) = R.A i j + mv R B C i * mv R B C j := rfl
@[simp] theorem Aterm_inl_inr (i : R.Vertices) (u : Unit) :
    Aterm R B P C (Sum.inl i) (Sum.inr u) = -contactVector R P i := rfl
@[simp] theorem Aterm_inr_inl (u : Unit) (j : R.Vertices) :
    Aterm R B P C (Sum.inr u) (Sum.inl j) = -contactVector R P j := rfl
@[simp] theorem Aterm_inr_inr (u w : Unit) : Aterm R B P C (Sum.inr u) (Sum.inr w) = 1 := rfl

/-- The canonical degrees on `S'`: `q + m` on `D`, `−1` on `P'`. -/
def qterm : R.Vertices ⊕ Unit → ℚ := Sum.elim (fun i => R.q i + mv R B C i) (fun _ => -1)

@[simp] theorem qterm_inl (i : R.Vertices) : qterm R B C (Sum.inl i) = R.q i + mv R B C i := rfl
@[simp] theorem qterm_inr (u : Unit) : qterm R B C (Sum.inr u) = -1 := rfl

theorem mv_dot_lamV (tc : TConfig R W B P C) :
    mv R B C ⬝ᵥ (fun i => lamTm R W B (Sum.inl i)) = lamT R B (Cd R W B P C tc) := by
  rw [mv_dot, lamTm_inl_B, lamTm_inl_C R W B P C tc, zero_add]

/-- Rows of `A₀ λ†` from the rank-one identity: `(A₀ λ†)_j = q₀_j + a_j (1 − λ†_C)`. -/
theorem Mblock_mulVec_lamT (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C)
    (j : D0 R B) :
    (Mblock R B *ᵥ lamT R B) j =
      q0 R B j + vvec R B j * (1 - lamT R B (Cd R W B P C tc)) := by
  have h := congrFun (terminal_rankOne_identity R W B P p hp tc.toConfig) j
  rw [Matrix.add_mulVec, Pi.add_apply, Pi.add_apply] at h
  have hr : (vecMulVec (vvec R B) (vvec R B) *ᵥ lamT R B) j =
      vvec R B j * (vvec R B ⬝ᵥ lamT R B) := by
    simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]
  rw [hr, vvec_dot R W B P C p hp tc] at h
  linarith

/-- **The null equations on `S'`, computed on `S`** (manuscript lines 1205–1207): `A' μ = q'`. -/
theorem Aterm_mulVec_lamTm (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C) :
    Aterm R B P C *ᵥ lamTm R W B = qterm R B C := by
  have hc := tc.toConfig
  have hV := lamV_eq R W B P C tc
  have hpv := contactVector_eq_single R W B P hc
  have hmvdot := mv_dot_lamV R W B P C tc
  have hw3 := w_B_eq_three R W B P p hp hc
  funext a
  rcases a with i | u
  · rw [mulVec_sum_apply']
    simp only [Aterm_inl_inl, Aterm_inl_inr, lamTm_inr, qterm_inl]
    have hsplit : ∑ j, (R.A i j + mv R B C i * mv R B C j) * lamTm R W B (Sum.inl j) =
        (R.A *ᵥ fun j => lamTm R W B (Sum.inl j)) i +
          mv R B C i * (mv R B C ⬝ᵥ fun j => lamTm R W B (Sum.inl j)) := by
      simp only [Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
        mul_assoc]
    rw [hsplit, hmvdot, hV]
    have hpi : contactVector R P i = (if i = W then 1 else 0) + (if i = B then 1 else 0) := by
      rw [hpv, Pi.add_apply, Pi.single_apply, Pi.single_apply]
    rw [hpi]
    by_cases hiB : i = B
    · subst i
      rw [mulVec_ext_C, dotProduct_sub, vvec_dot R W B P C p hp tc, dotProduct_single,
        vvec_apply R W B P C p hp tc, if_neg (Cd_ne_Wd R W B P C tc).symm, mv_B R W B P C tc,
        if_neg hc.hWB.symm, if_pos rfl]
      show _ = R.w B - 2 + 1
      rw [hw3]
      ring
    · have hrow : (R.A *ᵥ ext R B 0 (lamT R B - Pi.single (Wd R W B P hc) 1)) i =
          -(vvec R B ⟨i, hiB⟩) * 0 +
            (Mblock R B *ᵥ (lamT R B - Pi.single (Wd R W B P hc) 1)) ⟨i, hiB⟩ :=
        mulVec_ext_val R B 0 _ ⟨i, hiB⟩
      rw [hrow, Matrix.mulVec_sub, Pi.sub_apply, Matrix.mulVec_single_one, Matrix.transpose_apply,
        Mblock_apply_Wd R W B P hc, Mblock_mulVec_lamT R W B P C p hp tc,
        vvec_apply R W B P C p hp tc]
      have hq0 : q0 R B ⟨i, hiB⟩ = R.q i := rfl
      rw [hq0, if_neg hiB]
      by_cases hiC : i = C
      · have e1 : (⟨i, hiB⟩ : D0 R B) = Cd R W B P C tc := Subtype.ext hiC
        have e2 : (⟨i, hiB⟩ : D0 R B) ≠ Wd R W B P hc := by
          intro h
          have h' : i = W := congrArg Subtype.val h
          rw [hiC] at h'
          exact tc.C_ne_W h'
        have hmv : mv R B C i = 1 := by
          rw [hiC]
          exact mv_C R W B P C tc
        have hiW : i ≠ W := by
          rw [hiC]
          exact tc.C_ne_W
        rw [if_pos e1, if_neg e2, hmv, if_neg hiW]
        ring
      · have e1 : (⟨i, hiB⟩ : D0 R B) ≠ Cd R W B P C tc :=
          fun h => hiC (congrArg Subtype.val h)
        rw [if_neg e1, mv_of_ne R B C i hiB hiC]
        by_cases hiW : i = W
        · have e2 : (⟨i, hiB⟩ : D0 R B) = Wd R W B P hc := Subtype.ext hiW
          have hqW : R.q i = 0 := by
            show R.w i - 2 = 0
            rw [hiW, hc.hW2]
            norm_num
          rw [if_pos e2, if_pos hiW, hqW]
          ring
        · have e2 : (⟨i, hiB⟩ : D0 R B) ≠ Wd R W B P hc :=
            fun h => hiW (congrArg Subtype.val h)
          rw [if_neg e2, if_neg hiW]
          ring
  · rw [mulVec_sum_apply']
    simp only [Aterm_inr_inl, Aterm_inr_inr, lamTm_inr, qterm_inr]
    have hsum : ∑ j, -contactVector R P j * lamTm R W B (Sum.inl j) =
        -(contactVector R P ⬝ᵥ fun j => lamTm R W B (Sum.inl j)) := by
      simp only [dotProduct, neg_mul, Finset.sum_neg_distrib]
    rw [hsum, hpv, add_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul,
      lamTm_inl_W R W B P C tc, lamTm_inl_B]
    ring

/-! ### The square gain (eq:isolated-mixed-terminal-gain) -/

theorem lamTm_dot_qterm (tc : TConfig R W B P C) :
    lamTm R W B ⬝ᵥ qterm R B C = lamT R B ⬝ᵥ q0 R B + lamT R B (Cd R W B P C tc) + 2 := by
  have hV := lamV_eq R W B P C tc
  have hmvdot := mv_dot_lamV R W B P C tc
  rw [dot_sum']
  simp only [lamTm_inr, qterm_inr, qterm_inl]
  have h1 : ∑ j, lamTm R W B (Sum.inl j) * (R.q j + mv R B C j) =
      (fun j => lamTm R W B (Sum.inl j)) ⬝ᵥ R.q +
        mv R B C ⬝ᵥ (fun j => lamTm R W B (Sum.inl j)) := by
    simp only [dotProduct, mul_add, Finset.sum_add_distrib, mul_comm]
  rw [h1, hmvdot, hV, dot_ext, zero_mul, zero_add]
  have hq : (fun i : D0 R B => R.q i.1) = q0 R B := rfl
  rw [hq, sub_dotProduct, single_dotProduct, q0_Wd R W B P tc.toConfig]
  ring

/-- eq:isolated-mixed-terminal-gain: `K_{X₁}² − K_X² = μᵀq' − 1 − λᵀq = 2(2η(1−η) + 2h − 1)/(4h−1)`. -/
theorem terminal_gain_eq (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C) :
    lamTm R W B ⬝ᵥ qterm R B C - 1 - R.q ⬝ᵥ R.lam =
      2 * (2 * muC R B * (1 - muC R B) + 2 * gC R B - 1) / (4 * gC R B - 1) := by
  have hc := tc.toConfig
  have hql : R.q ⬝ᵥ R.lam = (bC R B - 2) * muC R B + q0 R B ⬝ᵥ lam0 R B := by
    have h1 := Lsq_eq_block R B
    have h2 := R.Lsq_eq_Ksq_add_dot
    linarith
  rw [lamTm_dot_qterm R W B P C tc, hql, lamT_Cd R W B P C p hp tc]
  unfold lamT
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul, lam0_eq R B, dotProduct_add, dotProduct_smul,
    smul_eq_mul, q0_dot_wv R B, dotProduct_comm (wv R B) (q0 R B), q0_dot_wv R B,
    dotProduct_comm (q0 R B) (theta R B)]
  unfold bC
  rw [w_B_eq_three R W B P p hp hc]
  have hg := (gC_pos R B).ne'
  have h4 : 4 * gC R B - 1 ≠ 0 := by
    have := half_lt_gC R W B P p hp hc
    intro h
    linarith
  have hs : vvec R B ⬝ᵥ theta R B = muC R B / gC R B - 1 := by
    have hmu := muC_eq_gC_mul_one_add R W B P p hp hc
    field_simp
    linarith
  rw [hs, t_eq R W B P p hp hc, terminal_epsilon_eq R W B P p hp hc]
  field_simp
  ring

theorem terminal_gain_pos' (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C) :
    0 < lamTm R W B ⬝ᵥ qterm R B C - 1 - R.q ⬝ᵥ R.lam := by
  rw [terminal_gain_eq R W B P C p hp tc]
  exact terminal_gain_pos R W B P p hp tc.toConfig

/-- `1 − λ†_C = ε` (the degree of the new anticanonical class on `E`, manuscript line 1211). -/
theorem one_sub_lamT_Cd (p : ℕ) [CharP k p] (hp : 0 < p) (tc : TConfig R W B P C) :
    1 - lamT R B (Cd R W B P C tc) = epsT R B := by
  rw [lamT_Cd R W B P C p hp tc]
  have ht := one_add_t_pos R W B P p hp tc.toConfig
  have hε : epsT R B * (1 + vvec R B ⬝ᵥ wv R B) = 1 - vvec R B ⬝ᵥ theta R B := by
    unfold epsT
    exact div_mul_cancel₀ _ ht.ne'
  linarith

end Terminal

/-! ## Part B: the retained family on the blowup `S'` and its contraction -/

section OnBlowup

variable [DecidableRel R.graph.Adj] (C : R.Vertices) (tc : TConfig R W B P C)
  {S' : NormalProjectiveSurface k} {σ : S'.toScheme ⟶ R.S.toScheme} {E : S'.PrimeCurve}
  {hcon : IsContraction S' R.S σ E} {hS' : ∀ s : S'.Point, RegularPoint S'.toScheme s}
  (hE : IsMinusOneCurve hS' E) (L : ContractionLifts hcon hS')
  {x : R.S.Point} (himg : σ.base '' (E : Set S'.toScheme) = {x})
  (hxB : x ∈ (B.1 : Set R.S.toScheme)) (hxC : x ∈ (C.1 : Set R.S.toScheme))

/-! ### Intersection numbers on `S` in terms of the datum -/

theorem A_eq_neg_pair (i j : R.Vertices) :
    R.A i j = -(R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
      (R.S.primeCurveCartier R.hreg j.1) : ℚ) := rfl

theorem graph_adj_iff (i j : R.Vertices) :
    R.graph.Adj i j ↔ i ≠ j ∧ 0 < R.S.intersectionPairing R.hreg
      (R.S.primeCurveCartier R.hreg i.1) (R.S.primeCurveCartier R.hreg j.1) :=
  curveIncidenceGraph_adj_iff_pairing_pos R.S R.hreg (fun i : R.Vertices => i.val)
    Subtype.val_injective

include tc in
/-- `B · C = 1`. -/
theorem pair_B_C (p : ℕ) [CharP k p] (hp : 0 < p) :
    R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg B.1)
      (R.S.primeCurveCartier R.hreg C.1) = 1 := by
  have h := A_B_apply R W B P C p hp tc C
  rw [if_neg tc.C_ne_B, if_pos rfl, A_eq_neg_pair] at h
  have h' : (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg B.1)
      (R.S.primeCurveCartier R.hreg C.1) : ℚ) = 1 := by linarith
  exact_mod_cast h'

include tc in
/-- `D_i · B = 0` for `i ∉ {B, C}`. -/
theorem disjoint_B_of_ne (p : ℕ) [CharP k p] (hp : 0 < p) (i : R.Vertices) (hiB : i ≠ B)
    (hiC : i ≠ C) : Disjoint (i.1 : Set R.S.toScheme) (B.1 : Set R.S.toScheme) := by
  have h := A_B_apply R W B P C p hp tc i
  rw [if_neg hiB, if_neg hiC, A_symm R B i, A_eq_neg_pair] at h
  have h' : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
      (R.S.primeCurveCartier R.hreg B.1) = 0 := by
    have : (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
        (R.S.primeCurveCartier R.hreg B.1) : ℚ) = 0 := by linarith
    exact_mod_cast this
  exact (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint R.S R.hreg
    i.1 B.1 (fun e => hiB (Subtype.ext e))).mp h'

include tc in
/-- `P · C = 0`. -/
theorem disjoint_P_C : Disjoint (P : Set R.S.toScheme) (C.1 : Set R.S.toScheme) := by
  have h0 : R.contact P C = 0 := tc.hP0 C tc.C_ne_W tc.C_ne_B
  have h' : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg P)
      (R.S.primeCurveCartier R.hreg C.1) = 0 := by
    rw [R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
    exact h0
  have hne : P ≠ C.1 := fun e => tc.hP.2 (e ▸ C.2)
  exact (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint R.S R.hreg
    P C.1 hne).mp h'

/-! ### Multiplicities at the node -/

include himg hxB hxC hE tc in
theorem mult_B_C (p : ℕ) [CharP k p] (hp : 0 < p) : L.mult B.1 = 1 ∧ L.mult C.1 = 1 := by
  have hB : 0 < L.mult B.1 := L.mult_pos B.1 ⟨x, hxB, by rw [himg]; exact Set.mem_singleton x⟩
  have hC : 0 < L.mult C.1 := L.mult_pos C.1 ⟨x, hxC, by rw [himg]; exact Set.mem_singleton x⟩
  have hne : B.1 ≠ C.1 := fun e => tc.C_ne_B (Subtype.ext e.symm)
  exact L.mult_eq_one_of_pair_one hE hne (pair_B_C R W B P C tc p hp) hB hC

include himg hxB tc in
theorem mult_of_ne (p : ℕ) [CharP k p] (hp : 0 < p) (i : R.Vertices) (hiB : i ≠ B) (hiC : i ≠ C) :
    L.mult i.1 = 0 := by
  apply L.mult_eq_zero i.1
  rw [himg, Set.disjoint_singleton_right]
  exact fun hx => Set.disjoint_left.mp (disjoint_B_of_ne R W B P C tc p hp i hiB hiC) hx hxB

include himg hxB tc in
theorem mult_W (p : ℕ) [CharP k p] (hp : 0 < p) : L.mult W.1 = 0 :=
  mult_of_ne R W B P C tc L himg hxB p hp W tc.hWB tc.C_ne_W.symm

include himg hxC tc in
theorem mult_P : L.mult P = 0 := by
  apply L.mult_eq_zero P
  rw [himg, Set.disjoint_singleton_right]
  exact fun hx => Set.disjoint_left.mp (disjoint_P_C R W B P C tc) hx hxC

include himg hxB hxC hE tc in
theorem mult_eq_mv (p : ℕ) [CharP k p] (hp : 0 < p) (i : R.Vertices) :
    (L.mult i.1 : ℚ) = mv R B C i := by
  by_cases hiB : i = B
  · subst i
    rw [(mult_B_C R W B P C tc hE L himg hxB hxC p hp).1, mv_B R W B P C tc]
    norm_num
  · by_cases hiC : i = C
    · subst i
      rw [(mult_B_C R W B P C tc hE L himg hxB hxC p hp).2, mv_C R W B P C tc]
      norm_num
    · rw [mult_of_ne R W B P C tc L himg hxB p hp i hiB hiC, mv_of_ne R B C i hiB hiC]
      norm_num

include himg hxB hxC hE tc in
theorem mult_le_one (p : ℕ) [CharP k p] (hp : 0 < p) (i : R.Vertices) : L.mult i.1 ≤ 1 := by
  by_cases hiB : i = B
  · subst i
    rw [(mult_B_C R W B P C tc hE L himg hxB hxC p hp).1]
  · by_cases hiC : i = C
    · subst i
      rw [(mult_B_C R W B P C tc hE L himg hxB hxC p hp).2]
    · rw [mult_of_ne R W B P C tc L himg hxB p hp i hiB hiC]
      omega

/-! ### The retained family on `S'` -/

/-- The retained family `{D_i'} ∪ {P'}` of strict transforms, indexed by `D ⊕ {P}`. -/
def famT : R.Vertices ⊕ Unit → S'.PrimeCurve := Sum.elim (fun i => L.lift i.1) (fun _ => L.lift P)

@[simp] theorem famT_inl (i : R.Vertices) : famT R P L (Sum.inl i) = L.lift i.1 := rfl
@[simp] theorem famT_inr (u : Unit) : famT R P L (Sum.inr u) = L.lift P := rfl

include tc in
theorem famT_injective : Function.Injective (famT R P L) := by
  rintro (i | u) (j | w) h
  · exact congrArg Sum.inl (Subtype.ext (L.lift_injective h))
  · exfalso
    have e : i.1 = P := L.lift_injective h
    exact tc.hP.2 (e ▸ i.2)
  · exfalso
    have e : P = j.1 := L.lift_injective h
    exact tc.hP.2 (e ▸ j.2)
  · rfl

theorem famT_ne_E (j : R.Vertices ⊕ Unit) : famT R P L j ≠ E := by
  rcases j with i | u
  · exact L.lift_ne_E i.1
  · exact L.lift_ne_E P

include himg hxB hxC hE tc in
theorem famT_rational (p : ℕ) [CharP k p] (hp : 0 < p) (j : R.Vertices ⊕ Unit) :
    ∃ e : (famT R P L j).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (famT R P L j).toSpec := by
  rcases j with i | u
  · exact L.lift_rational i.1 (mult_le_one R W B P C tc hE L himg hxB hxC p hp i)
      (R.exceptional_rational i.1 i.2)
  · exact L.lift_rational P (by rw [mult_P R W B P C tc L himg hxC]; exact zero_le_one)
      tc.hP.1.isoProjectiveLine

/-! ### The intersection matrix and canonical degrees on `S'` -/

include himg hxB hxC hE tc in
/-- The negative intersection matrix of the retained family is `A + m mᵀ` (with `−p` contacts and
`P'² = −1`). -/
theorem negIntersectionMatrix_famT (p : ℕ) [CharP k p] (hp : 0 < p) :
    negIntersectionMatrix S' hS' (famT R P L) = Aterm R B P C := by
  have hmP := mult_P R W B P C tc L himg hxC
  funext a b
  rcases a with i | u <;> rcases b with j | w
  · show -(S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift i.1))
      (S'.primeCurveCartier hS' (L.lift j.1)) : ℚ) = R.A i j + mv R B C i * mv R B C j
    rw [L.pair_lift_lift hE, mult_eq_mv R W B P C tc hE L himg hxB hxC p hp,
      mult_eq_mv R W B P C tc hE L himg hxB hxC p hp, A_eq_neg_pair]
    ring
  · show -(S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift i.1))
      (S'.primeCurveCartier hS' (L.lift P)) : ℚ) = -contactVector R P i
    rw [L.pair_lift_lift hE, hmP, Nat.cast_zero, mul_zero, sub_zero,
      R.S.intersectionPairing_primeCurve R.hreg]
    rfl
  · show -(S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift P))
      (S'.primeCurveCartier hS' (L.lift j.1)) : ℚ) = -contactVector R P j
    rw [L.pair_lift_lift hE, hmP, Nat.cast_zero, zero_mul, sub_zero,
      R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
    rfl
  · show -(S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift P))
      (S'.primeCurveCartier hS' (L.lift P)) : ℚ) = 1
    rw [L.pair_lift_lift hE, hmP, Nat.cast_zero, zero_mul, sub_zero, pairing_P_P R P tc.hP.1]
    norm_num

variable (hcon hS') in
/-- `K = σ^*K_S + E` on `S'`. -/
def IsCanonicalLift (K : CartierDivisor S'.toScheme) : Prop :=
  letI : GenericPointPreserving σ := ⟨hcon.birational.map_genericPoint⟩
  K = DominantCartierPullback.pullbackHom σ R.KS + S'.primeCurveCartier hS' E

include hE in
theorem exists_canonicalLift : ∃ K : CartierDivisor S'.toScheme,
    Nonempty (cartierDivisorModule S'.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S'.structureMorphism 2) ∧
    IsCanonicalLift R hcon hS' K :=
  ContractionLifts.exists_canonical hcon hS' hE R.KS R.eKS

include himg hxB hxC hE tc in
/-- The canonical degrees of the retained family are `q + m` and `−1`. -/
theorem canonicalDegreeVector_famT (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (hK : IsCanonicalLift R hcon hS' K) :
    canonicalDegreeVector S' (famT R P L) K = qterm R B C := by
  funext a
  rcases a with i | u
  · show ((L.lift i.1).intersectionNumber K : ℚ) = R.q i + mv R B C i
    rw [L.intersectionNumber_lift_canonical hE R.KS K hK i.1,
      mult_eq_mv R W B P C tc hE L himg hxB hxC p hp]
    have h := R.Kdeg_exceptional i
    unfold ResolutionDatum.Kdeg at h
    rw [h]
  · show ((L.lift P).intersectionNumber K : ℚ) = -1
    rw [L.intersectionNumber_lift_canonical hE R.KS K hK P, mult_P R W B P C tc L himg hxC]
    have h := Kdeg_eq_neg_one_of_isMinusOne R P tc.hP.1
    unfold ResolutionDatum.Kdeg at h
    rw [h]
    norm_num

include himg hxB hxC hE tc in
/-- **The null equations on `S'`** (manuscript lines 1205–1207). -/
theorem null_equations (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (hK : IsCanonicalLift R hcon hS' K) :
    negIntersectionMatrix S' hS' (famT R P L) *ᵥ lamTm R W B =
      canonicalDegreeVector S' (famT R P L) K := by
  rw [negIntersectionMatrix_famT R W B P C tc hE L himg hxB hxC p hp,
    canonicalDegreeVector_famT R W B P C tc hE L himg hxB hxC p hp K hK]
  exact Aterm_mulVec_lamTm R W B P C p hp tc

/-! ### The class `H₁ = −(K_{S'} + Σ μ_j G_j)` -/

/-- `H₁ ∈ N¹(S')_ℚ`. -/
def LnumT (K : CartierDivisor S'.toScheme) : S'.NumericalClassGroup :=
  adjustedClass S' hS' (famT R P L) K (lamTm R W B)

include himg hxB hxC hE tc in
theorem LsqT_eq (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (hK : IsCanonicalLift R hcon hS' K) :
    S'.numericalIntersectionBilinForm hS' (LnumT R W B P L K) (LnumT R W B P L K) =
      (S'.intersectionPairing hS' K K : ℚ) + lamTm R W B ⬝ᵥ qterm R B C := by
  unfold LnumT
  rw [square_formula S' hS' (famT R P L) K (lamTm R W B)
    (null_equations R W B P C tc hE L himg hxB hxC p hp K hK),
    NefNullCurveNegativeSquare.cartierClass_pairing S' hS',
    canonicalDegreeVector_famT R W B P C tc hE L himg hxB hxC p hp K hK]

include himg hxB hxC hE tc in
/-- eq:isolated-mixed-terminal-gain: `H₁² > L² > 0`. -/
theorem Lsq_lt_LsqT (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (eK : cartierDivisorModule S'.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S'.structureMorphism 2)
    (hK : IsCanonicalLift R hcon hS' K) :
    R.Lsq < S'.numericalIntersectionBilinForm hS' (LnumT R W B P L K) (LnumT R W B P L K) := by
  rw [LsqT_eq R W B P C tc hE L himg hxB hxC p hp K hK]
  have hK2 : (S'.intersectionPairing hS' K K : ℚ) =
      (R.S.intersectionPairing R.hreg R.KS R.KS : ℚ) - 1 := by
    have h := hcon.canonical_square_eq_sub_one hS' hE K R.KS eK R.eKS
    exact_mod_cast h
  rw [hK2, ← R.Ksq_eq_intersectionPairing]
  have h1 := R.Lsq_eq_Ksq_add_dot
  have h2 := terminal_gain_pos' R W B P C p hp tc
  linarith

include himg hxB hxC hE tc in
theorem LsqT_pos (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (eK : cartierDivisorModule S'.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S'.structureMorphism 2)
    (hK : IsCanonicalLift R hcon hS' K) :
    0 < S'.numericalIntersectionBilinForm hS' (LnumT R W B P L K) (LnumT R W B P L K) :=
  lt_trans R.Lsq_pos (Lsq_lt_LsqT R W B P C tc hE L himg hxB hxC p hp K eK hK)

/-! ### Degrees of `H₁` -/

include himg hxB hxC hE tc in
/-- `H₁ · G_j = 0` on the retained family. -/
theorem degree_LnumT_famT (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (hK : IsCanonicalLift R hcon hS' K) (j : R.Vertices ⊕ Unit) :
    S'.numericalRestrictionDegree (famT R P L j) (LnumT R W B P L K) = 0 := by
  unfold LnumT
  rw [degree_formula S' hS' (famT R P L) K (lamTm R W B) (famT R P L j)]
  have hnull := congrFun (null_equations R W B P C tc hE L himg hxB hxC p hp K hK) j
  have hrow : (fun l => ((famT R P L j).intersectionNumber
      (S'.primeCurveCartier hS' (famT R P L l)) : ℚ)) ⬝ᵥ lamTm R W B =
      -(negIntersectionMatrix S' hS' (famT R P L) *ᵥ lamTm R W B) j := by
    simp only [Matrix.mulVec, dotProduct, negIntersectionMatrix,
      NullCurveIntersectionMatrix.intersectionMatrix, Matrix.neg_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]
    ring
  rw [hrow, hnull]
  unfold canonicalDegreeVector
  ring

include himg hxB hxC hE tc in
/-- `H₁ · E = ε > 0` (manuscript line 1211). -/
theorem degree_LnumT_E (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (hK : IsCanonicalLift R hcon hS' K) :
    S'.numericalRestrictionDegree E (LnumT R W B P L K) = epsT R B := by
  unfold LnumT
  rw [degree_formula S' hS' (famT R P L) K (lamTm R W B) E,
    ContractionLifts.intersectionNumber_E_canonical (hb := hcon) hE R.KS K hK]
  have hdot : (fun l => (E.intersectionNumber (S'.primeCurveCartier hS' (famT R P L l)) : ℚ)) ⬝ᵥ
      lamTm R W B = lamT R B (Cd R W B P C tc) := by
    rw [dot_sum']
    have h1 : ∀ i : R.Vertices,
        (E.intersectionNumber (S'.primeCurveCartier hS' (famT R P L (Sum.inl i))) : ℚ) =
          mv R B C i := by
      intro i
      rw [famT_inl, ← S'.intersectionPairing_primeCurve hS', L.pair_lift_E hE,
        mult_eq_mv R W B P C tc hE L himg hxB hxC p hp]
    have h2 : (E.intersectionNumber (S'.primeCurveCartier hS' (famT R P L (Sum.inr ()))) : ℚ) = 0 := by
      rw [famT_inr, ← S'.intersectionPairing_primeCurve hS', L.pair_lift_E hE,
        mult_P R W B P C tc L himg hxC, Nat.cast_zero]
    simp only [h1, h2, lamTm_inr, zero_mul, add_zero]
    exact mv_dot_lamV R W B P C tc
  rw [hdot]
  have := one_sub_lamT_Cd R W B P C p hp tc
  linarith

theorem Lnum_eq_adjusted :
    R.Lnum = adjustedClass R.S R.hreg (fun i : R.Vertices => i.val) R.KS R.lam := by
  rw [R.Lnum_eq]
  rfl

include himg hxB hxC hE tc in
/-- `H₁ · Q̃ = L·Q + Σ_i (λ_i − μ_i) (Q·D_i) + 2 (Q·P) − m_Q ε` for every prime curve `Q` of `S`. -/
theorem degree_LnumT_lift (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (hK : IsCanonicalLift R hcon hS' K) (Q : R.S.PrimeCurve) :
    S'.numericalRestrictionDegree (L.lift Q) (LnumT R W B P L K) =
      R.Ldeg Q + ∑ i, (R.lam i - lamTm R W B (Sum.inl i)) *
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ) +
        2 * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) -
        L.mult Q * epsT R B := by
  unfold LnumT
  rw [degree_formula S' hS' (famT R P L) K (lamTm R W B) (L.lift Q),
    L.intersectionNumber_lift_canonical hE R.KS K hK Q]
  have hL : R.Ldeg Q = -(Q.intersectionNumber R.KS : ℚ) -
      (fun i : R.Vertices => (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ)) ⬝ᵥ
        R.lam := by
    rw [← R.numericalRestrictionDegree_Lnum, Lnum_eq_adjusted, degree_formula]
  have hdot : (fun l => ((L.lift Q).intersectionNumber
      (S'.primeCurveCartier hS' (famT R P L l)) : ℚ)) ⬝ᵥ lamTm R W B =
      ∑ i, ((Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ) -
        L.mult Q * mv R B C i) * lamTm R W B (Sum.inl i) +
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) * (-2) := by
    rw [dot_sum']
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [famT_inl, ← S'.intersectionPairing_primeCurve hS', L.pair_lift_lift hE,
        mult_eq_mv R W B P C tc hE L himg hxB hxC p hp, R.S.intersectionPairing_primeCurve R.hreg,
        mul_comm (L.mult Q : ℚ)]
    · rw [famT_inr, lamTm_inr, ← S'.intersectionPairing_primeCurve hS', L.pair_lift_lift hE,
        mult_P R W B P C tc L himg hxC, Nat.cast_zero, zero_mul, sub_zero,
        R.S.intersectionPairing_primeCurve R.hreg]
  rw [hL, hdot]
  have hsum : ∑ i, ((Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ) -
      L.mult Q * mv R B C i) * lamTm R W B (Sum.inl i) =
      (fun i : R.Vertices => (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ)) ⬝ᵥ
        (fun i => lamTm R W B (Sum.inl i)) -
        L.mult Q * (mv R B C ⬝ᵥ fun i => lamTm R W B (Sum.inl i)) := by
    simp only [dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  have hsum2 : ∑ i, (R.lam i - lamTm R W B (Sum.inl i)) *
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ) =
      (fun i : R.Vertices => (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ)) ⬝ᵥ
        R.lam -
        (fun i : R.Vertices => (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ)) ⬝ᵥ
          (fun i => lamTm R W B (Sum.inl i)) := by
    simp only [dotProduct, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hsum, hsum2, mv_dot_lamV R W B P C tc]
  have hε := one_sub_lamT_Cd R W B P C p hp tc
  linear_combination (-(L.mult Q : ℚ)) * hε

include tc in
theorem lam_sub_lamTm_nonneg (p : ℕ) [CharP k p] (hp : 0 < p) (i : R.Vertices) :
    0 ≤ R.lam i - lamTm R W B (Sum.inl i) := by
  by_cases hB : i = B
  · subst i
    rw [lamTm_inl_B, sub_zero]
    exact R.lam_nonneg B
  · rw [lamTm_inl_of_ne R W B i hB]
    have h := lamT_le_lam0 R W B P p hp tc.toConfig ⟨i, hB⟩
    have hl : lam0 R B ⟨i, hB⟩ = R.lam i := rfl
    rw [hl] at h
    split_ifs <;> linarith

include himg hxB hxC hE tc in
/-- `H₁ · Q̃ > 0` for every exterior prime curve `Q ≠ P` of `S`. -/
theorem degree_LnumT_lift_pos (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (hK : IsCanonicalLift R hcon hS' K) (Q : R.S.PrimeCurve) (hQ : ¬ IsExceptionalCurve R.π Q)
    (hQP : Q ≠ P) : 0 < S'.numericalRestrictionDegree (L.lift Q) (LnumT R W B P L K) := by
  rw [degree_LnumT_lift R W B P C tc hE L himg hxB hxC p hp K hK Q]
  have h1 := Ldeg_pos R Q hQ
  have hQB : 0 ≤ (Q.intersectionNumber (R.S.primeCurveCartier R.hreg B.1) : ℚ) :=
    intersectionNumber_nonneg_of_ne R Q B.1 (fun h => hQ (h ▸ B.2))
  have hm : (L.mult Q : ℚ) ≤ (Q.intersectionNumber (R.S.primeCurveCartier R.hreg B.1) : ℚ) := by
    have hnn : (0 : ℤ) ≤ S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift B.1))
        (S'.primeCurveCartier hS' (L.lift Q)) :=
      PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg S' hS' _ _
        (fun h => hQ (by rw [← L.lift_injective h]; exact B.2))
    have h := L.pair_lift_lift hE B.1 Q
    rw [(mult_B_C R W B P C tc hE L himg hxB hxC p hp).1, Nat.cast_one, one_mul,
      R.S.intersectionPairing_primeCurve R.hreg] at h
    have h0 : (0 : ℚ) ≤ (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift B.1))
        (S'.primeCurveCartier hS' (L.lift Q)) : ℚ) := by exact_mod_cast hnn
    linarith
  have hsum : muC R B * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg B.1) : ℚ) ≤
      ∑ i, (R.lam i - lamTm R W B (Sum.inl i)) *
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ) := by
    have hterm : ∀ i ∈ (Finset.univ : Finset R.Vertices), 0 ≤ (R.lam i - lamTm R W B (Sum.inl i)) *
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.1) : ℚ) :=
      fun i _ => mul_nonneg (lam_sub_lamTm_nonneg R W B P C tc p hp i)
        (intersectionNumber_nonneg_of_ne R Q i.1 (fun h => hQ (h ▸ i.2)))
    have hB := Finset.single_le_sum hterm (Finset.mem_univ B)
    rw [lamTm_inl_B, sub_zero] at hB
    exact hB
  have hQP' : 0 ≤ (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) :=
    intersectionNumber_nonneg_of_ne R Q P hQP
  have hη := muC_nonneg' R B
  have hεη := terminal_epsilon_lt_muC R W B P p hp tc.toConfig
  have hm0 : (0 : ℚ) ≤ L.mult Q := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hm hη, mul_le_mul_of_nonneg_left hεη.le hm0]

include himg hxB hxC hE tc in
/-- `H₁` is nef. -/
theorem degree_LnumT_nonneg (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (hK : IsCanonicalLift R hcon hS' K) (Q' : S'.PrimeCurve) :
    0 ≤ S'.numericalRestrictionDegree Q' (LnumT R W B P L K) := by
  by_cases hQE : Q' = E
  · rw [hQE, degree_LnumT_E R W B P C tc hE L himg hxB hxC p hp K hK]
    exact (terminal_epsilon_pos R W B P p hp tc.toConfig).le
  · obtain ⟨Q, rfl⟩ := L.lift_surj Q' hQE
    by_cases hQ : IsExceptionalCurve R.π Q
    · have h := degree_LnumT_famT R W B P C tc hE L himg hxB hxC p hp K hK (Sum.inl ⟨Q, hQ⟩)
      rw [famT_inl] at h
      exact le_of_eq h.symm
    · by_cases hQP : Q = P
      · have h := degree_LnumT_famT R W B P C tc hE L himg hxB hxC p hp K hK (Sum.inr ())
        rw [famT_inr] at h
        rw [hQP]
        exact le_of_eq h.symm
      · exact (degree_LnumT_lift_pos R W B P C tc hE L himg hxB hxC p hp K hK Q hQ hQP).le

include himg hxB hxC hE tc in
/-- The null locus of `H₁` is exactly the retained family. -/
theorem degree_LnumT_eq_zero_iff (p : ℕ) [CharP k p] (hp : 0 < p) (K : CartierDivisor S'.toScheme)
    (hK : IsCanonicalLift R hcon hS' K) (Q' : S'.PrimeCurve) :
    S'.numericalRestrictionDegree Q' (LnumT R W B P L K) = 0 ↔ ∃ j, Q' = famT R P L j := by
  constructor
  · intro h0
    by_cases hQE : Q' = E
    · exfalso
      rw [hQE, degree_LnumT_E R W B P C tc hE L himg hxB hxC p hp K hK] at h0
      exact (terminal_epsilon_pos R W B P p hp tc.toConfig).ne' h0
    · obtain ⟨Q, rfl⟩ := L.lift_surj Q' hQE
      by_cases hQ : IsExceptionalCurve R.π Q
      · exact ⟨Sum.inl ⟨Q, hQ⟩, rfl⟩
      · by_cases hQP : Q = P
        · exact ⟨Sum.inr (), by rw [hQP]; rfl⟩
        · exfalso
          exact (degree_LnumT_lift_pos R W B P C tc hE L himg hxB hxC p hp K hK Q hQ hQP).ne' h0
  · rintro ⟨j, rfl⟩
    exact degree_LnumT_famT R W B P C tc hE L himg hxB hxC p hp K hK j

/-! ### A Cartier multiple of `H₁` -/

/-- The rational Weil divisor `K + Σ_j μ_j G_j = −H₁`. -/
def DweilT (K : CartierDivisor S'.toScheme) : S'.RationalWeilDivisor :=
  S'.rationalCartierToWeilHom K + ∑ j, Finsupp.single (famT R P L j) (lamTm R W B j)

theorem rationalWeilNumericalMap_DweilT (K : CartierDivisor S'.toScheme) :
    S'.rationalWeilNumericalMap hS' (DweilT R W B P L K) = -(LnumT R W B P L K) := by
  unfold DweilT LnumT adjustedClass curveCombination
  rw [map_add, map_sum, rationalWeilNumericalMap_rationalCartier' S' hS', neg_neg]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finsupp.smul_single_one, map_smul, rationalWeilNumericalMap_single' S' hS']

theorem cartierClass_HmT (K : CartierDivisor S'.toScheme) {n : ℕ} {Hm : CartierDivisor S'.toScheme}
    (hHm : S'.rationalCartierToWeilHom Hm = -((n : ℚ) • DweilT R W B P L K)) :
    NefNullCurveNegativeSquare.cartierClass S' Hm = (n : ℚ) • LnumT R W B P L K := by
  rw [← rationalWeilNumericalMap_rationalCartier' S' hS', hHm, map_neg, map_smul,
    rationalWeilNumericalMap_DweilT, smul_neg, neg_neg]

theorem intersectionNumber_HmT (K : CartierDivisor S'.toScheme) {n : ℕ}
    {Hm : CartierDivisor S'.toScheme}
    (hHm : S'.rationalCartierToWeilHom Hm = -((n : ℚ) • DweilT R W B P L K)) (Q : S'.PrimeCurve) :
    (Q.intersectionNumber Hm : ℚ) =
      (n : ℚ) * S'.numericalRestrictionDegree Q (LnumT R W B P L K) := by
  rw [← numericalRestrictionDegree_cartierClass S' hS' Q Hm, cartierClass_HmT R W B P L K hHm,
    map_smul, smul_eq_mul]

theorem intersectionPairing_HmT (K : CartierDivisor S'.toScheme) {n : ℕ}
    {Hm : CartierDivisor S'.toScheme}
    (hHm : S'.rationalCartierToWeilHom Hm = -((n : ℚ) • DweilT R W B P L K)) :
    (S'.intersectionPairing hS' Hm Hm : ℚ) =
      (n : ℚ) ^ 2 * S'.numericalIntersectionBilinForm hS' (LnumT R W B P L K) (LnumT R W B P L K) := by
  rw [← NefNullCurveNegativeSquare.cartierClass_pairing S' hS' Hm Hm, cartierClass_HmT R W B P L K hHm,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  ring

/-! ### The retained family is an SNC forest of `ρ(S') − 1` rational curves -/

include himg hxB hxC hE tc in
/-- Pairwise intersections of the retained family are at most one. -/
theorem pair_famT_le_one (a b : R.Vertices ⊕ Unit) (hab : a ≠ b) :
    S'.intersectionPairing hS' (S'.primeCurveCartier hS' (famT R P L a))
      (S'.primeCurveCartier hS' (famT R P L b)) ≤ 1 := by
  have hforest := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  have hmP := mult_P R W B P C tc L himg hxC
  have hcontact : ∀ i : R.Vertices, (R.contact P i : ℚ) ≤ 1 := by
    intro i
    by_cases hiW : i = W
    · rw [hiW, tc.hPW]
      norm_num
    · by_cases hiB : i = B
      · rw [hiB, tc.hPB]
        norm_num
      · rw [tc.hP0 i hiW hiB]
        norm_num
  suffices h : (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (famT R P L a))
      (S'.primeCurveCartier hS' (famT R P L b)) : ℚ) ≤ 1 by exact_mod_cast h
  rcases a with i | u <;> rcases b with j | w
  · rw [famT_inl, famT_inl, L.pair_lift_lift hE]
    have h1 : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
        (R.S.primeCurveCartier R.hreg j.1) ≤ 1 :=
      hforest.2.2.2 i j (fun h => hab (congrArg Sum.inl h))
    have h1' : (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
        (R.S.primeCurveCartier R.hreg j.1) : ℚ) ≤ 1 := by exact_mod_cast h1
    have h2 : (0 : ℚ) ≤ (L.mult i.1 : ℚ) * L.mult j.1 := by positivity
    linarith
  · rw [famT_inl, famT_inr, L.pair_lift_lift hE, hmP, Nat.cast_zero, mul_zero, sub_zero,
      R.S.intersectionPairing_primeCurve R.hreg]
    exact hcontact i
  · rw [famT_inr, famT_inl, L.pair_lift_lift hE, hmP, Nat.cast_zero, zero_mul, sub_zero,
      R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
    exact hcontact j
  · exact absurd rfl hab

include himg hxB hxC hE tc in
/-- The incidence graph of the retained family is a forest (manuscript lines 1214–1216): `W'` is a
leaf on `P'`, `P'` is then a leaf on `B'`, and the remaining edges are edges of the exceptional
forest `D` (with the edge `B–C` deleted). -/
theorem famT_acyclic (p : ℕ) [CharP k p] (hp : 0 < p) :
    (curveIncidenceGraph (famT R P L)).IsAcyclic := by
  classical
  have hinj := famT_injective R W B P C tc L
  have hadj : ∀ a b, (curveIncidenceGraph (famT R P L)).Adj a b ↔
      a ≠ b ∧ 0 < S'.intersectionPairing hS' (S'.primeCurveCartier hS' (famT R P L a))
        (S'.primeCurveCartier hS' (famT R P L b)) :=
    fun a b => curveIncidenceGraph_adj_iff_pairing_pos S' hS' (famT R P L) hinj
  have hRac : R.graph.IsAcyclic :=
    (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.2.1
  have hmP := mult_P R W B P C tc L himg hxC
  have hmW := mult_W R W B P C tc L himg hxB p hp
  -- the pairing of `P'` with `D_j'`
  have hPj : ∀ j : R.Vertices, (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift P))
      (S'.primeCurveCartier hS' (L.lift j.1)) : ℚ) = (R.contact P j : ℚ) := by
    intro j
    rw [L.pair_lift_lift hE, hmP, Nat.cast_zero, zero_mul, sub_zero,
      R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
  -- Step 1: `W'` is a leaf attached to `P'`.
  refine isAcyclic_of_leaf (Sum.inl W) (Sum.inr ()) ?_
    ((curveIncidenceGraph (famT R P L)).deleteEdges {e | Sum.inl W ∈ e}) ?_ ?_
  · rintro (j | u) h
    · exfalso
      obtain ⟨hne, hpos⟩ := (hadj _ _).mp h
      have hWj : W ≠ j := fun e => hne (by rw [e])
      have h1 := L.pair_lift_lift hE W.1 j.1
      rw [hmW, Nat.cast_zero, zero_mul, sub_zero] at h1
      have h2 : R.A W j = 0 := by
        rw [A_W_apply R W B P tc.toConfig j, if_neg hWj.symm]
      rw [A_eq_neg_pair, neg_eq_zero] at h2
      have h3 : (0 : ℚ) < (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift W.1))
          (S'.primeCurveCartier hS' (L.lift j.1)) : ℚ) := by exact_mod_cast hpos
      rw [h1, h2] at h3
      exact lt_irrefl _ h3
    · rfl
  · intro a b hab ha hb
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hab, ?_⟩
    simp only [Set.mem_setOf_eq, Sym2.mem_iff, not_or]
    exact ⟨fun h => ha h.symm, fun h => hb h.symm⟩
  -- Step 2: `P'` is a leaf attached to `B'` once the edges at `W'` are removed.
  refine isAcyclic_of_leaf (Sum.inr ()) (Sum.inl B) ?_
    (((curveIncidenceGraph (famT R P L)).deleteEdges {e | Sum.inl W ∈ e}).deleteEdges
      {e | Sum.inr () ∈ e}) ?_ ?_
  · rintro (j | u) h
    · rw [SimpleGraph.deleteEdges_adj] at h
      obtain ⟨h, hnotW⟩ := h
      simp only [Set.mem_setOf_eq, Sym2.mem_iff, not_or] at hnotW
      have hjW : j ≠ W := fun e => hnotW.2 (by rw [e])
      obtain ⟨-, hpos⟩ := (hadj _ _).mp h
      have h3 : (0 : ℚ) < (R.contact P j : ℚ) := by
        rw [← hPj j]
        exact_mod_cast hpos
      refine Classical.byContradiction fun hjB => ?_
      have hjB' : j ≠ B := fun e => hjB (by rw [e])
      rw [tc.hP0 j hjW hjB', Int.cast_zero] at h3
      exact lt_irrefl _ h3
    · exact absurd h (SimpleGraph.irrefl _)
  · intro a b hab ha hb
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hab, ?_⟩
    simp only [Set.mem_setOf_eq, Sym2.mem_iff, not_or]
    exact ⟨fun h => ha h.symm, fun h => hb h.symm⟩
  -- Step 3: the remaining edges are edges of the exceptional forest `D`.
  refine isAcyclic_of_inl_edges hRac _ ?_
  intro a b hab
  rw [SimpleGraph.deleteEdges_adj, SimpleGraph.deleteEdges_adj] at hab
  obtain ⟨⟨hab, -⟩, hnotP⟩ := hab
  simp only [Set.mem_setOf_eq, Sym2.mem_iff, not_or] at hnotP
  rcases a with i | u
  · rcases b with j | w
    · refine ⟨i, j, rfl, rfl, ?_⟩
      obtain ⟨hne, hpos⟩ := (hadj _ _).mp hab
      have hij : i ≠ j := fun e => hne (by rw [e])
      rw [graph_adj_iff]
      refine ⟨hij, ?_⟩
      have h1 := L.pair_lift_lift hE i.1 j.1
      have h3 : (0 : ℚ) < (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift i.1))
          (S'.primeCurveCartier hS' (L.lift j.1)) : ℚ) := by exact_mod_cast hpos
      rw [h1] at h3
      have h4 : (0 : ℚ) ≤ (L.mult i.1 : ℚ) * L.mult j.1 := by positivity
      have h5 : (0 : ℚ) < (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
          (R.S.primeCurveCartier R.hreg j.1) : ℚ) := by linarith
      exact_mod_cast h5
    · exact absurd rfl hnotP.2
  · exact absurd rfl hnotP.1

include hE hcon hS' in
/-- `#G + 1 = ρ(S')`: the retained family has `ρ(S') − 1 = ρ(S)` members. -/
theorem card_famT (p : ℕ) [CharP k p] (hp : 0 < p) :
    Fintype.card (R.Vertices ⊕ Unit) + 1 = S'.picardRank := by
  have h1 : S'.picardRank = R.S.picardRank + 1 := hcon.picardRank_eq_add_one hS' hE
  have h2 : R.S.picardRank = 1 + Nat.card R.Vertices := by
    have := R.hmin.picardRank_eq_of_klt R.hklt p hp
    rw [R.hrank] at this
    exact this
  rw [h1, h2, Fintype.card_sum, Fintype.card_unit, Nat.card_eq_fintype_card]
  omega

/-! ### The contraction (Theorem 2.6) on `S'` -/

include himg hxB hxC hE tc in
/-- **The terminal exchange contraction** (manuscript lines 1203–1216), performed on the blowup
`S'`: the family `{P', W', B'} ∪ (D − W − B)'` with coefficients `(−2, −1, 0, λ†)` is contracted by
a Cartier multiple of `H₁` to a rank-one klt del Pezzo surface `X₁`, with all conclusions of
Theorem 2.6. -/
theorem anticanonicalContraction_terminal (p : ℕ) [CharP k p] (hp : 0 < p)
    (K : CartierDivisor S'.toScheme)
    (eK : cartierDivisorModule S'.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S'.structureMorphism 2)
    (hK : IsCanonicalLift R hcon hS' K) :
    ∃ (Y : NormalProjectiveSurface k) (f : S'.toScheme ⟶ Y.toScheme)
      (hproper : IsProper f) (hbir : IsBirationalScheme f),
      f ≫ Y.structureMorphism = S'.structureMorphism ∧ IsIso f.c ∧ IsBirational f ∧
      (∀ y : Y.toScheme, IsConnected (f.base ⁻¹' {y})) ∧
      (∀ Q : S'.PrimeCurve, IsExceptionalCurve f Q ↔ ∃ j, Q = famT R P L j) ∧
      IsKltDelPezzo Y ∧ Y.picardRank = 1 ∧
      letI : IsProper f := hproper
      letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      let KY : Y.WeilDivisor :=
        BirationalWeilPushforward.pushforward f hbir (S'.cartierToWeilHom K)
      IsKltWithCanonicalDivisor Y KY ∧ Y.QAmple (-rationalizeWeilDivisor Y KY) ∧
      ∃ hK' : Y.QCartier (rationalizeWeilDivisor Y KY),
        QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK' =
          S'.rationalCartierToWeilHom K +
            ∑ j, Finsupp.single (famT R P L j) (lamTm R W B j) := by
  obtain ⟨n, Hm, hn, hHm⟩ := exists_cartier_multiple_T S' hS' (DweilT R W B P L K)
  have hinj := famT_injective R W B P C tc L
  have hrat := famT_rational R W B P C tc hE L himg hxB hxC p hp
  have hlam := lamTm_lt_one R W B P C p hp tc
  have hHm' : S'.rationalCartierToWeilHom Hm = -((n : ℚ) • (S'.rationalCartierToWeilHom K +
      ∑ j, Finsupp.single (famT R P L j) (lamTm R W B j))) := hHm
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hnef : Positivity.IsNef S'.structureMorphism
      (cartierDivisorInvertibleSheaf S'.toScheme Hm) := by
    rw [Positivity.isNef_iff_forall_primeCurve]
    intro Q
    rw [← Q.intersectionNumber_eq_restrictionDegree]
    have h1 := intersectionNumber_HmT R W B P L K hHm Q
    have h2 := degree_LnumT_nonneg R W B P C tc hE L himg hxB hxC p hp K hK Q
    have : (0 : ℚ) ≤ (Q.intersectionNumber Hm : ℚ) := by
      rw [h1]
      exact mul_nonneg hnpos.le h2
    exact_mod_cast this
  have hsq : 0 < S'.intersectionPairing hS' Hm Hm := by
    have h1 := intersectionPairing_HmT R W B P L K hHm
    have h2 := LsqT_pos R W B P C tc hE L himg hxB hxC p hp K eK hK
    have : (0 : ℚ) < (S'.intersectionPairing hS' Hm Hm : ℚ) := by
      rw [h1]
      exact mul_pos (pow_pos hnpos 2) h2
    exact_mod_cast this
  have hnull : ∀ Q : S'.PrimeCurve,
      Q.restrictionDegree (cartierDivisorInvertibleSheaf S'.toScheme Hm) = 0 ↔
        ∃ j, Q = famT R P L j := by
    intro Q
    rw [← Q.intersectionNumber_eq_restrictionDegree,
      ← degree_LnumT_eq_zero_iff R W B P C tc hE L himg hxB hxC p hp K hK Q]
    have h1 := intersectionNumber_HmT R W B P L K hHm Q
    constructor
    · intro h0
      have h2 : (n : ℚ) * S'.numericalRestrictionDegree Q (LnumT R W B P L K) = 0 := by
        rw [← h1, h0, Int.cast_zero]
      exact (mul_eq_zero.mp h2).resolve_left hnpos.ne'
    · intro h0
      have h2 : (Q.intersectionNumber Hm : ℚ) = 0 := by
        rw [h1, h0, mul_zero]
      exact_mod_cast h2
  exact anticanonicalContraction p hp S' hS' K eK (famT R P L) hinj hrat
    (famT_acyclic R W B P C tc hE L himg hxB hxC p hp)
    (pair_famT_le_one R W B P C tc hE L himg hxB hxC) (card_famT R (hcon := hcon) hE p hp)
    (lamTm R W B) hlam n hn Hm hHm' hnef hsq hnull

/-! ### Pairings of the retained curves used for the images and the second contraction -/

include himg hxB hxC hE tc in
theorem pair_W'_P' :
    (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift W.1))
      (S'.primeCurveCartier hS' (L.lift P)) : ℚ) = 1 := by
  rw [L.pair_lift_lift hE, mult_P R W B P C tc L himg hxC, Nat.cast_zero, mul_zero, sub_zero,
    R.S.intersectionPairing_primeCurve R.hreg]
  have h : R.contact P W = 1 := tc.hPW
  exact_mod_cast h

include himg hxB hxC hE tc in
theorem pair_P'_B' :
    (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift P))
      (S'.primeCurveCartier hS' (L.lift B.1)) : ℚ) = 1 := by
  rw [L.pair_lift_lift hE, mult_P R W B P C tc L himg hxC, Nat.cast_zero, zero_mul, sub_zero,
    R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
  have h : R.contact P B = 1 := tc.hPB
  exact_mod_cast h

include himg hxB hxC hE tc in
/-- `W'² = −2`. -/
theorem pair_W'_W' (p : ℕ) [CharP k p] (hp : 0 < p) :
    (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift W.1))
      (S'.primeCurveCartier hS' (L.lift W.1)) : ℚ) = -2 := by
  rw [L.pair_lift_lift hE, mult_W R W B P C tc L himg hxB p hp, Nat.cast_zero, mul_zero, sub_zero]
  have h : R.A W W = 2 := by
    rw [R.A_diag]
    exact tc.hW2
  rw [A_eq_neg_pair] at h
  linarith

/-! ### The singular points of `X₁` -/

section Contraction

variable (Y : NormalProjectiveSurface k) (f : S'.toScheme ⟶ Y.toScheme) [IsProper f]
  (hbir : IsBirationalScheme f) (hf : f ≫ Y.structureMorphism = S'.structureMorphism)
  (hconn : ∀ y : Y.toScheme, IsConnected (f.base ⁻¹' {y}))
  (hexc : ∀ Q : S'.PrimeCurve, IsExceptionalCurve f Q ↔ ∃ j, Q = famT R P L j)

include hexc in
theorem exceptional_famT (j : R.Vertices ⊕ Unit) : IsExceptionalCurve f (famT R P L j) :=
  (hexc _).mpr ⟨j, rfl⟩

include hbir hf hconn hexc tc in
/-- The image points of the contraction are counted by the components of the incidence graph. -/
theorem ncard_imagePoints_T :
    (ActualExceptionalLocus.imagePoints f).ncard =
      Nat.card (curveIncidenceGraph (famT R P L)).ConnectedComponent := by
  have hinj := famT_injective R W B P C tc L
  let eV : R.Vertices ⊕ Unit ≃ ActualExceptionalIncidence.Vertices f :=
    Equiv.ofBijective (fun j => ⟨famT R P L j, exceptional_famT R P L Y f hexc j⟩)
      ⟨fun a b h => hinj (congrArg Subtype.val h),
       fun v => by
        obtain ⟨j, hj⟩ := (hexc v.1).mp v.2
        exact ⟨j, Subtype.ext hj.symm⟩⟩
  let eG : curveIncidenceGraph (famT R P L) ≃g ActualExceptionalIncidence.graph f := by
    refine ⟨eV, ?_⟩
    intro a b
    show (eV a ≠ eV b ∧ ((famT R P L a : Set S'.toScheme) ∩ famT R P L b).Nonempty) ↔
      (a ≠ b ∧ ((famT R P L a : Set S'.toScheme) ∩ famT R P L b).Nonempty)
    exact and_congr eV.injective.ne_iff Iff.rfl
  rw [← ActualExceptionalLocus.component_count f hbir hf hconn,
    Nat.card_congr (ActualExceptionalIncidence.supportComponentEquiv f hbir)]
  exact Nat.card_congr eG.connectedComponentEquiv.symm

variable (hS') in
include hbir hf hconn hS' in
theorem singularPoints_subset_imagePoints_T [IsIso f.c] :
    (Y.singularPoints : Set Y.Point) ⊆ ActualExceptionalLocus.imagePoints f := by
  letI : IsIso (f ∣_ ActualExceptionalLocus.complementOpen f hbir) :=
    ActualExceptionalLocus.isIso_complementOpen f hbir hf hconn
  have h := RegularPointsOnIsomorphismOpen.singularPoints_subset_compl Y f
    (ActualExceptionalLocus.complementOpen f hbir) hS'
  intro y hy
  have hy' := h hy
  exact not_not.mp hy'

include hexc tc in
/-- Two retained curves with positive pairing have the same image point. -/
theorem image_famT_eq_of_pair_pos (a b : R.Vertices ⊕ Unit)
    (hpos : 0 < (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (famT R P L a))
      (S'.primeCurveCartier hS' (famT R P L b)) : ℚ)) :
    f.base (famT R P L a).genericPoint = f.base (famT R P L b).genericPoint := by
  by_cases hab : a = b
  · rw [hab]
  · have hne : famT R P L a ≠ famT R P L b := fun h => hab (famT_injective R W B P C tc L h)
    have hint : ((famT R P L a : Set S'.toScheme) ∩ famT R P L b).Nonempty := by
      rw [← Set.not_disjoint_iff_nonempty_inter]
      intro hd
      have h0 := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
        S' hS' _ _ hne).mpr hd
      rw [h0, Int.cast_zero] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨z, hza, hzb⟩ := hint
    rw [← image_eq_of_exceptional (exceptional_famT R P L Y f hexc a) hza,
      image_eq_of_exceptional (exceptional_famT R P L Y f hexc b) hzb]

include hbir hf hexc tc in
/-- The image of a retained curve with nonnegative coefficient is a singular point of `X₁`. -/
theorem image_famT_mem_singularPoints (K : CartierDivisor S'.toScheme)
    (eK : cartierDivisorModule S'.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S'.structureMorphism 2)
    (hK' : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      Y.QCartier (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (S'.cartierToWeilHom K))))
    (hpull : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      QCartierPullback.pullback f (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (S'.cartierToWeilHom K))) hK' =
        S'.rationalCartierToWeilHom K + ∑ j, Finsupp.single (famT R P L j) (lamTm R W B j))
    (j : R.Vertices ⊕ Unit) (hj : 0 ≤ lamTm R W B j) :
    f.base (famT R P L j).genericPoint ∈ Y.singularPoints := by
  letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
  letI : IsSmoothOfRelativeDimension 2 S'.structureMorphism :=
    S'.isSmoothOfRelativeDimension_two_of_regularPoints hS'
  have hexcj : IsExceptionalCurve f (famT R P L j) := exceptional_famT R P L Y f hexc j
  have hmem : f.base (famT R P L j).genericPoint ∈ ActualExceptionalLocus.imagePoints f :=
    ⟨_, (ActualExceptionalLocus.mem_primeSupport f _).mpr
      ⟨famT R P L j, hexcj, (famT R P L j).genericPoint_mem⟩, rfl⟩
  have hclosed : IsClosed ({f.base (famT R P L j).genericPoint} : Set Y.toScheme) :=
    ActualExceptionalLocus.imagePoint_isClosed f ⟨_, hmem⟩
  have hKYcan := isCanonicalWeilDivisor_pushforward_of_cartier S' Y f hf hbir K eK
  rw [Y.mem_singularPoints]
  intro hreg
  have hpos := RegularTargetCanonicalDiscrepancy.coefficient_pos_of_regular_closed_image S' Y f
    hbir hf K eK _ hKYcan hK' rfl (famT R P L j) hclosed hreg
  rw [hpull] at hpos
  have hval : (∑ l, Finsupp.single (famT R P L l) (lamTm R W B l)) (famT R P L j) =
      lamTm R W B j := by
    have h := sum_single_apply_eq (famT R P L) (famT_injective R W B P C tc L) (lamTm R W B) j
    simpa using h
  simp only [Finsupp.sub_apply, Finsupp.add_apply, hval] at hpos
  linarith

include himg hxB hxC hE hbir hf hconn hexc tc in
/-- Every image point is singular: the singular points of `X₁` are exactly the image points
(manuscript lines 1216–1219). -/
theorem singularPoints_eq_imagePoints_T [IsIso f.c] (p : ℕ) [CharP k p] (hp : 0 < p)
    (K : CartierDivisor S'.toScheme)
    (eK : cartierDivisorModule S'.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S'.structureMorphism 2)
    (hK' : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      Y.QCartier (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (S'.cartierToWeilHom K))))
    (hpull : letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      QCartierPullback.pullback f (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (S'.cartierToWeilHom K))) hK' =
        S'.rationalCartierToWeilHom K + ∑ j, Finsupp.single (famT R P L j) (lamTm R W B j)) :
    (Y.singularPoints : Set Y.Point) = ActualExceptionalLocus.imagePoints f := by
  apply Set.Subset.antisymm (singularPoints_subset_imagePoints_T hS' Y f hbir hf hconn)
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨Q, hQ, hzQ⟩ := (ActualExceptionalLocus.mem_primeSupport f z).mp hz
  obtain ⟨j, rfl⟩ := (hexc Q).mp hQ
  rw [image_eq_of_exceptional hQ hzQ]
  have hB : f.base (famT R P L (Sum.inl B)).genericPoint ∈ Y.singularPoints :=
    image_famT_mem_singularPoints R W B P C tc L Y f hbir hf hexc K eK hK' hpull (Sum.inl B)
      (by rw [lamTm_inl_B])
  have hPB : f.base (famT R P L (Sum.inr ())).genericPoint =
      f.base (famT R P L (Sum.inl B)).genericPoint :=
    image_famT_eq_of_pair_pos R W B P C tc L Y f hexc (Sum.inr ()) (Sum.inl B)
      (by rw [famT_inr, famT_inl, pair_P'_B' R W B P C tc hE L himg hxB hxC]; norm_num)
  rcases j with i | u
  · by_cases hiW : i = W
    · subst i
      have hWP : f.base (famT R P L (Sum.inl W)).genericPoint =
          f.base (famT R P L (Sum.inr ())).genericPoint :=
        image_famT_eq_of_pair_pos R W B P C tc L Y f hexc (Sum.inl W) (Sum.inr ())
          (by rw [famT_inl, famT_inr, pair_W'_P' R W B P C tc hE L himg hxB hxC]; norm_num)
      rw [hWP, hPB]
      exact hB
    · exact image_famT_mem_singularPoints R W B P C tc L Y f hbir hf hexc K eK hK' hpull
        (Sum.inl i) (lamTm_inl_nonneg R W B P C p hp tc i hiW)
  · rw [hPB]
    exact hB

end Contraction

/-! ### The component count: `#π₀(G) = #π₀(D)` (manuscript lines 1216–1219) -/

include tc in
theorem degree_B_eq_one : R.graph.degree B = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h : R.graph.neighborFinset B = {C} := by
    ext j
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    exact ⟨fun h => tc.hCu j h, fun h => h ▸ tc.hBC⟩
  rw [h, Finset.card_singleton]

include himg hxB hxC hE tc in
/-- The incidence graph of the retained family has as many components as the exceptional graph
`D`: deleting `B–C` splits `Δ` into `{B}` and `Δ − B`, and the path `W' – P' – B'` rejoins `W`,
`P`, `B`. -/
theorem card_components_famT (p : ℕ) [CharP k p] (hp : 0 < p) :
    Nat.card (curveIncidenceGraph (famT R P L)).ConnectedComponent =
      Nat.card R.graph.ConnectedComponent := by
  classical
  have hinj := famT_injective R W B P C tc L
  have hadj : ∀ a b, (curveIncidenceGraph (famT R P L)).Adj a b ↔
      a ≠ b ∧ 0 < S'.intersectionPairing hS' (S'.primeCurveCartier hS' (famT R P L a))
        (S'.primeCurveCartier hS' (famT R P L b)) :=
    fun a b => curveIncidenceGraph_adj_iff_pairing_pos S' hS' (famT R P L) hinj
  have hforest := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  have hRac : R.graph.IsAcyclic := hforest.2.2.1
  have hΓac := famT_acyclic R W B P C tc hE L himg hxB hxC p hp
  have hmP := mult_P R W B P C tc L himg hxC
  have hmv := mult_eq_mv R W B P C tc hE L himg hxB hxC p hp
  have hPj : ∀ j : R.Vertices, (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift P))
      (S'.primeCurveCartier hS' (L.lift j.1)) : ℚ) = (R.contact P j : ℚ) := by
    intro j
    rw [L.pair_lift_lift hE, hmP, Nat.cast_zero, zero_mul, sub_zero,
      R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
  have hij : ∀ i j : R.Vertices, (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift i.1))
      (S'.primeCurveCartier hS' (L.lift j.1)) : ℚ) =
      (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
        (R.S.primeCurveCartier R.hreg j.1) : ℚ) - mv R B C i * mv R B C j := by
    intro i j
    rw [L.pair_lift_lift hE, hmv i, hmv j]
  -- (1) the degree of `P'` is two
  have hdeg : (curveIncidenceGraph (famT R P L)).degree (Sum.inr ()) = 2 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hN : (curveIncidenceGraph (famT R P L)).neighborFinset (Sum.inr ()) =
        {Sum.inl W, Sum.inl B} := by
      ext a
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
      rcases a with j | u
      · rw [hadj]
        simp only [famT_inl, famT_inr]
        constructor
        · rintro ⟨-, hpos⟩
          have h3 : (0 : ℚ) < (R.contact P j : ℚ) := by
            rw [← hPj j]
            exact_mod_cast hpos
          by_cases hjW : j = W
          · exact Or.inl (by rw [hjW])
          by_cases hjB : j = B
          · exact Or.inr (by rw [hjB])
          exfalso
          rw [tc.hP0 j hjW hjB, Int.cast_zero] at h3
          exact lt_irrefl _ h3
        · rintro (h | h)
          · have hj : j = W := Sum.inl.inj h
            refine ⟨Sum.inr_ne_inl, ?_⟩
            have h3 : (0 : ℚ) < (R.contact P j : ℚ) := by
              rw [hj, tc.hPW]
              norm_num
            rw [← hPj j] at h3
            exact_mod_cast h3
          · have hj : j = B := Sum.inl.inj h
            refine ⟨Sum.inr_ne_inl, ?_⟩
            have h3 : (0 : ℚ) < (R.contact P j : ℚ) := by
              rw [hj, tc.hPB]
              norm_num
            rw [← hPj j] at h3
            exact_mod_cast h3
      · simp only [SimpleGraph.irrefl, false_iff, not_or]
        exact ⟨Sum.inr_ne_inl, Sum.inr_ne_inl⟩
    rw [hN, Finset.card_pair (fun h => tc.hWB (Sum.inl.inj h))]
  -- (2) the exceptional graph with the edge `B–C` deleted
  set G₀ : SimpleGraph R.Vertices := R.graph.deleteEdges {s(B, C)} with hG₀
  have hG₀ac : G₀.IsAcyclic := fun u c hc =>
    hRac (c.mapLe (SimpleGraph.deleteEdges_le _))
      ((SimpleGraph.Walk.mapLe_isCycle (SimpleGraph.deleteEdges_le _)).mpr hc)
  have hG₀adj : ∀ i j, G₀.Adj i j ↔ R.graph.Adj i j ∧ s(i, j) ≠ s(B, C) := by
    intro i j
    rw [hG₀, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  have hpairBC := pair_B_C R W B P C tc p hp
  -- (3) `Γ − P' ≃ G₀`
  have hΓG₀ : ∀ i j : R.Vertices,
      (curveIncidenceGraph (famT R P L)).Adj (Sum.inl i) (Sum.inl j) ↔ G₀.Adj i j := by
    intro i j
    rw [hadj, hG₀adj, graph_adj_iff]
    simp only [famT_inl]
    constructor
    · rintro ⟨hne, hpos⟩
      have hij' : i ≠ j := fun e => hne (by rw [e])
      have h3 : (0 : ℚ) < (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift i.1))
          (S'.primeCurveCartier hS' (L.lift j.1)) : ℚ) := by exact_mod_cast hpos
      rw [hij i j] at h3
      have h4 : (0 : ℚ) ≤ mv R B C i * mv R B C j :=
        mul_nonneg (mv_nonneg R B C i) (mv_nonneg R B C j)
      refine ⟨⟨hij', ?_⟩, ?_⟩
      · have : (0 : ℚ) < (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
            (R.S.primeCurveCartier R.hreg j.1) : ℚ) := by linarith
        exact_mod_cast this
      · intro hs
        rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst i
          subst j
          rw [mv_B R W B P C tc, mv_C R W B P C tc, hpairBC] at h3
          norm_num at h3
        · subst i
          subst j
          rw [mv_B R W B P C tc, mv_C R W B P C tc, R.S.intersectionPairing_symm R.hreg,
            hpairBC] at h3
          norm_num at h3
    · rintro ⟨⟨hij', hpos⟩, hs⟩
      refine ⟨fun e => hij' (Sum.inl.inj e), ?_⟩
      have hle : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.1)
          (R.S.primeCurveCartier R.hreg j.1) ≤ 1 := hforest.2.2.2 i j hij'
      have hmv0 : mv R B C i * mv R B C j = 0 := by
        by_cases hiB : i = B
        · have hjC : j ≠ C := fun e => hs (by rw [hiB, e])
          have hjB : j ≠ B := fun e => hij' (hiB.trans e.symm)
          rw [mv_of_ne R B C j hjB hjC, mul_zero]
        · by_cases hiC : i = C
          · have hjB : j ≠ B := fun e => hs (by rw [hiC, e, Sym2.eq_swap])
            have hjC : j ≠ C := fun e => hij' (hiC.trans e.symm)
            rw [mv_of_ne R B C j hjB hjC, mul_zero]
          · rw [mv_of_ne R B C i hiB hiC, zero_mul]
      have h3 : (0 : ℚ) < (S'.intersectionPairing hS' (S'.primeCurveCartier hS' (L.lift i.1))
          (S'.primeCurveCartier hS' (L.lift j.1)) : ℚ) := by
        rw [hij i j, hmv0, sub_zero]
        exact_mod_cast hpos
      exact_mod_cast h3
  let g : R.Vertices → ↥(({Sum.inr ()}ᶜ : Set (R.Vertices ⊕ Unit))) :=
    fun i => ⟨Sum.inl i, Sum.inl_ne_inr⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j h
      exact Sum.inl.inj (congrArg Subtype.val h)
    · rintro ⟨a, ha⟩
      rcases a with i | u
      · exact ⟨i, rfl⟩
      · exact absurd rfl (by cases u; exact ha)
  let e : G₀ ≃g (curveIncidenceGraph (famT R P L)).induce ({Sum.inr ()}ᶜ : Set (R.Vertices ⊕ Unit)) := by
    refine ⟨Equiv.ofBijective g hg, ?_⟩
    intro i j
    show (curveIncidenceGraph (famT R P L)).Adj (Sum.inl i) (Sum.inl j) ↔ G₀.Adj i j
    exact hΓG₀ i j
  -- (4) `G₀ − B = D − B` and `B` is isolated in `G₀`
  have hdegG₀ : G₀.degree B = 0 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero,
      Finset.eq_empty_iff_forall_not_mem]
    intro j hj
    rw [SimpleGraph.mem_neighborFinset, hG₀adj] at hj
    exact hj.2 (by rw [tc.hCu j hj.1])
  have hind : G₀.induce ({B}ᶜ : Set R.Vertices) = R.graph.induce ({B}ᶜ : Set R.Vertices) := by
    ext a b
    show G₀.Adj a.1 b.1 ↔ R.graph.Adj a.1 b.1
    rw [hG₀adj]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun hs => ?_⟩
      have hBmem : B ∈ s(a.1, b.1) := by
        rw [hs]
        exact Sym2.mem_mk_left _ _
      rcases Sym2.mem_iff.mp hBmem with hB | hB
      · exact a.2 hB.symm
      · exact b.2 hB.symm
  -- (5) counting
  have h1 := KltDP.Support.WeightedForestCore.deleteVertex_card_components
    (curveIncidenceGraph (famT R P L)) hΓac (Sum.inr ())
  rw [hdeg, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h1
  have h2 : Nat.card ((curveIncidenceGraph (famT R P L)).induce
      ({Sum.inr ()}ᶜ : Set (R.Vertices ⊕ Unit))).ConnectedComponent =
      Nat.card G₀.ConnectedComponent :=
    (Nat.card_congr e.connectedComponentEquiv).symm
  have h3 := KltDP.Support.WeightedForestCore.deleteVertex_card_components G₀ hG₀ac B
  rw [hdegG₀, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h3
  have h4 := KltDP.Support.WeightedForestCore.deleteVertex_card_components R.graph hRac B
  rw [degree_B_eq_one R W B P C tc, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h4
  have h5 : Nat.card (G₀.induce ({B}ᶜ : Set R.Vertices)).ConnectedComponent =
      Nat.card (R.graph.induce ({B}ᶜ : Set R.Vertices)).ConnectedComponent := by
    rw [hind]
  omega

/-! ### The resolution datum of `X₁` -/

include himg hxB hxC hE tc L in
/-- **Theorem 4.6, terminal case, datum form** (manuscript lines 1194–1219): a resolution datum
`R₁` of `X₁` with `ρ(R₁.S) < ρ(R.S)` and `#Sing(X₁) = #Sing(X)`. The strict Picard decrease comes
from the two `(-1)`-curves `P'` and (after contracting `P'`) the image of `W'`, both exceptional
for `S' → X₁`; the second uses strict transforms along the union's Castelnuovo contraction of `P'`
(`HasContractionLifts`). -/
theorem exists_terminal_datum (hL : HasContractionLifts k) (p : ℕ) [CharP k p] (hp : 0 < p)
    (K : CartierDivisor S'.toScheme)
    (eK : cartierDivisorModule S'.toScheme K ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S'.structureMorphism 2)
    (hK : IsCanonicalLift R hcon hS' K) :
    ∃ R₁ : ResolutionDatum k, R₁.S.picardRank < R.S.picardRank ∧
      R₁.X.singularPoints.card = R.X.singularPoints.card := by
  obtain ⟨Y, f, hproper, hbir, hf, hcY, hbirational, hconn, hexc, hDP, hrankY, hrest⟩ :=
    anticanonicalContraction_terminal R W B P C tc hE L himg hxB hxC p hp K eK hK
  letI : IsProper f := hproper
  letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
  letI : IsIso f.c := hcY
  obtain ⟨hKY, -, hK', hpull⟩ := hrest
  have hres : IsResolution S' Y f := ⟨hf, hS', hbirational⟩
  -- `P'` is an exceptional `(-1)`-curve
  have hP'exc : IsExceptionalCurve f (L.lift P) := (hexc _).mpr ⟨Sum.inr (), rfl⟩
  have hPminus : IsMinusOneCurve hcon.regular P := tc.hP.1
  have hP'minus : IsMinusOneCurve hS' (L.lift P) :=
    L.lift_minusOne hE P hPminus (mult_P R W B P C tc L himg hxC)
  -- contract it
  obtain ⟨S₁, b₁, hb₁⟩ :=
    (GeneralResolution.contraction k).exists_contraction S' hS' (L.lift P) hP'minus
  obtain ⟨f₁, hfac, hres₁⟩ := hres.of_contraction (contractionUniversal k) hb₁ hP'exc
  obtain ⟨L₁⟩ := hL hb₁ hS' hP'minus
  -- the image `W₁` of `W'` is again an exceptional `(-1)`-curve
  have hW'exc : IsExceptionalCurve f (L.lift W.1) := (hexc _).mpr ⟨Sum.inl W, rfl⟩
  have hW'ne : L.lift W.1 ≠ L.lift P := fun h => tc.hP.2 ((L.lift_injective h) ▸ W.2)
  obtain ⟨W₁, hW₁⟩ := L₁.lift_surj (L.lift W.1) hW'ne
  have hm₁ : L₁.mult W₁ = 1 := by
    have h := L₁.pair_E_lift hP'minus W₁
    rw [hW₁, S'.intersectionPairing_symm hS', pair_W'_P' R W B P C tc hE L himg hxB hxC] at h
    exact_mod_cast h.symm
  have hW₁sq : (S₁.intersectionPairing hb₁.regular (S₁.primeCurveCartier hb₁.regular W₁)
      (S₁.primeCurveCartier hb₁.regular W₁) : ℚ) = -1 := by
    have h := L₁.pair_lift_lift hP'minus W₁ W₁
    rw [hW₁, pair_W'_W' R W B P C tc hE L himg hxB hxC p hp, hm₁] at h
    push_cast at h
    linarith
  have hW₁minus : IsMinusOneCurve hb₁.regular W₁ := by
    refine ⟨?_, ?_⟩
    · obtain ⟨e₁, he₁⟩ := L₁.lift_iso W₁ (by rw [hm₁])
      have hrat : ∃ e : (L₁.lift W₁).toScheme ≅ projectiveSpace k 1,
          e.hom ≫ projectiveSpaceToSpec k 1 = (L₁.lift W₁).toSpec := by
        rw [hW₁]
        exact L.lift_rational W.1 (by
          rw [mult_W R W B P C tc L himg hxB p hp]; exact zero_le_one)
          (R.exceptional_rational W.1 W.2)
      obtain ⟨e₂, he₂⟩ := hrat
      refine ⟨e₁.symm ≪≫ e₂, ?_⟩
      rw [Iso.trans_hom, Category.assoc, he₂, ← he₁, Iso.symm_hom, Iso.inv_hom_id_assoc]
    · have h : W₁.intersectionNumber (S₁.primeCurveCartier hb₁.regular W₁) = -1 := by
        rw [← S₁.intersectionPairing_primeCurve hb₁.regular]
        exact_mod_cast hW₁sq
      exact h
  have hW₁exc : IsExceptionalCurve f₁ W₁ := by
    obtain ⟨y, hy⟩ := hW'exc
    refine ⟨y, ?_⟩
    rw [← L₁.image_lift W₁, hW₁, ← hy, ← hfac]
    ext z
    simp only [Set.mem_image, Scheme.comp_base_apply]
    constructor
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨b₁.base v, ⟨v, hv, rfl⟩, rfl⟩
  -- the minimal resolution
  obtain ⟨T, g, hmin, hlt⟩ := exists_minimalResolution_ncard_lt hres₁ W₁ hW₁exc hW₁minus
  have hlt₁ := hb₁.ncard_exceptionalCurves_lt_of_actualMaps hres hres₁ hfac hP'exc
  let R₁ : ResolutionDatum k := ⟨T, Y, g, hmin, hDP, hrankY⟩
  refine ⟨R₁, ?_, ?_⟩
  · show T.picardRank < R.S.picardRank
    have h1 : T.picardRank = 1 + Nat.card (ActualExceptionalIncidence.Vertices g) := by
      have := hmin.picardRank_eq_of_klt ⟨_, hKY⟩ p hp
      rw [hrankY] at this
      exact this
    have h2 : Nat.card (ActualExceptionalIncidence.Vertices g) =
        {Q : T.PrimeCurve | IsExceptionalCurve g Q}.ncard := Set.Nat.card_coe_set_eq _
    have h3 : {Q : S'.PrimeCurve | IsExceptionalCurve f Q}.ncard =
        Fintype.card (R.Vertices ⊕ Unit) := by
      rw [← Set.Nat.card_coe_set_eq, ← Nat.card_eq_fintype_card]
      have hinj := famT_injective R W B P C tc L
      let eV : R.Vertices ⊕ Unit ≃ {Q : S'.PrimeCurve | IsExceptionalCurve f Q} :=
        Equiv.ofBijective (fun j => ⟨famT R P L j, (hexc _).mpr ⟨j, rfl⟩⟩)
          ⟨fun a b h => hinj (congrArg Subtype.val h),
           fun v => by
            obtain ⟨j, hj⟩ := (hexc v.1).mp v.2
            exact ⟨j, Subtype.ext hj.symm⟩⟩
      exact Nat.card_congr eV.symm
    have h4 := card_famT R (hcon := hcon) hE p hp
    have h5 : S'.picardRank = R.S.picardRank + 1 := hcon.picardRank_eq_add_one hS' hE
    omega
  · show Y.singularPoints.card = R.X.singularPoints.card
    have hnX : R.X.singularPoints.card = Nat.card R.graph.ConnectedComponent :=
      (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.1
    have hset := singularPoints_eq_imagePoints_T R W B P C tc hE L himg hxB hxC Y f hbir hf hconn
      hexc p hp K eK hK' hpull
    have himgc := ncard_imagePoints_T R W B P C tc L Y f hbir hf hconn hexc
    have hcomp := card_components_famT R W B P C tc hE L himg hxB hxC p hp
    rw [← Set.ncard_coe_Finset, hset, himgc, hcomp, hnX]

end OnBlowup

/-! ## The terminal case of Theorem 4.6, given the two geometric inputs -/

/-- Points of `B ∩ C` are closed. -/
theorem isClosed_singleton_of_mem_inter {X : NormalProjectiveSurface k}
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x) {B C : X.PrimeCurve} (hBC : B ≠ C)
    {x : X.Point} (hxB : x ∈ (B : Set X.toScheme)) (hxC : x ∈ (C : Set X.toScheme)) :
    IsClosed ({x} : Set X.toScheme) := by
  have h := B.range_intersectionToSurface_finite_and_isClosed (X.primeCurveCartier hX C)
    (X.primeCurveCartier_hasRegularEquations hX C) (X.notInSupport_of_ne hX hBC)
  apply h.2
  rw [B.range_intersectionToSurface, X.primeCurveCartier_support hX]
  exact ⟨hxB, hxC⟩

end IsolatedNodeExchange

open IsolatedNodeExchange

/-- **The terminal case `d = 1` of Theorem 4.6** (manuscript lines 1141–1145 and 1194–1219), given
the two standard geometric inputs about point blowups (`HasPointBlowups`: the blowup of a regular
surface at a closed point exists with exceptional `(-1)`-curve; `HasContractionLifts`: strict
transforms along a contraction). -/
theorem isolatedExchangeTerminalHyp_of_blowups {k : Type u} [Field k] [IsAlgClosed k]
    (hB : HasPointBlowups k) (hL : HasContractionLifts k) (R : ResolutionDatum k)
    [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p] (hp : 0 < p) :
    IsolatedExchangeTerminalHyp R := by
  classical
  intro W B P hP hW2 hWiso hB3 hPW hPB hP0 hd1
  have hWB : W ≠ B := by
    intro h
    rw [h] at hW2
    linarith
  have hc : Config R W B P := ⟨hP, hW2, hWiso, hWB, hPW, hPB, hP0, hB3⟩
  obtain ⟨C, hBC, hCu⟩ := exists_unique_neighbour R B hd1
  have tc : TConfig R W B P C := ⟨hc, hBC, hCu⟩
  -- the node `x = B ∩ C`
  have hne : B.1 ≠ C.1 := fun e => tc.C_ne_B (Subtype.ext e.symm)
  have hint : ((B.1 : Set R.S.toScheme) ∩ C.1).Nonempty := by
    rw [← Set.not_disjoint_iff_nonempty_inter]
    intro hd
    have h0 := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      R.S R.hreg B.1 C.1 hne).mpr hd
    rw [pair_B_C R W B P C tc p hp] at h0
    exact one_ne_zero h0
  obtain ⟨x, hxB, hxC⟩ := hint
  have hxclosed : IsClosed ({x} : Set R.S.toScheme) :=
    isClosed_singleton_of_mem_inter R.hreg hne hxB hxC
  obtain ⟨S', σ, E, hS', hcon, hE, himg⟩ := hB R.S R.hreg x hxclosed
  obtain ⟨L⟩ := hL hcon hS' hE
  obtain ⟨K, ⟨eK⟩, hK⟩ := exists_canonicalLift R (hcon := hcon) hE
  obtain ⟨R₁, hρ, hcount⟩ :=
    exists_terminal_datum R W B P C tc hE L himg hxB hxC hL p hp K eK hK
  exact ⟨R₁, hρ, le_of_eq hcount.symm⟩

/-- **Theorem 4.6 in the interface form of Theorem 7.1**, given the two geometric inputs. -/
theorem isolatedExchangeHyp_of_blowups {k : Type u} [Field k] [IsAlgClosed k]
    (hB : HasPointBlowups k) (hL : HasContractionLifts k) (R : ResolutionDatum k)
    [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p] (hp : 0 < p) : IsolatedExchangeHyp R :=
  isolatedExchangeHyp_of_terminal R p hp (isolatedExchangeTerminalHyp_of_blowups hB hL R p hp)

/-! ## Input (ii) from the union's Stacks 0AGQ literal -/

/-- **`HasPointBlowups` follows from the union's Stacks 0AGQ literal `BlowupRegularPointLiteral`.**
The blowup of a regular projective surface at a closed point is the union's glued point blowup
(`PointBlowupExceptionalPrimeStalk.sourceSurface`, a `NormalProjectiveSurface` by regularity,
properness and Hartshorne's projectivity literal); by `BlowupExceptional.exists_minusOne_of_literal`
its exceptional curve `E` is a `(-1)`-curve over the centre, and since the centre fibre is
irreducible, the blowdown is the contraction of `E`. -/
theorem hasPointBlowups_of_literal {k : Type u} [Field k] [IsAlgClosed k]
    (hA : KltDP.Literature.Stacks.BlowupRegularPointLiteral k) : HasPointBlowups k := by
  intro T hT x hx
  letI : IsSmoothOfRelativeDimension 2 T.structureMorphism :=
    T.isSmoothOfRelativeDimension_two_of_regularPoints hT
  letI : IsSmooth T.structureMorphism := IsSmoothOfRelativeDimension.isSmooth 2 T.structureMorphism
  letI : IsIntegral T.toScheme := T.integral
  -- an affine chart around `x`
  let U : T.toScheme.Opens := (T.toScheme.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (T.toScheme.affineCover.map x)
  have hxU : x ∈ U := T.toScheme.affineCover.covers x
  let q : PrimeSpectrum Γ(T.toScheme, U) := hU.primeIdealOf ⟨x, hxU⟩
  haveI hq : q.asIdeal.IsMaximal := isMaximal_primeIdealOf_of_isClosed T.toScheme hU ⟨x, hxU⟩ hx
  have hxq : hU.fromSpec.base q = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hclosed' : IsClosed ({hU.fromSpec.base q} : Set T.toScheme) := by
    rw [hxq]
    exact hx
  -- the glued blowup as a surface
  let S' : NormalProjectiveSurface k :=
    PointBlowupExceptionalPrimeStalk.sourceSurface T hU.fromSpec q hclosed'
  let c : PointBlowupChart T.toScheme x :=
    { R := Γ(T.toScheme, U), j := hU.fromSpec, q := q, isClosed := hclosed', base_eq := hxq }
  let b : S'.toScheme ⟶ T.toScheme := PointBlowupGluing.projection hU.fromSpec q hclosed'
  have hb : IsPointBlowupAt S' T b x :=
    ⟨rfl, c, Iso.refl _, by rw [Iso.refl_hom, Category.id_comp]; rfl⟩
  have hS' : ∀ s : S'.Point, RegularPoint S'.toScheme s :=
    SchemePointBlowup.IsAt.source_regular T (SchemePointBlowup.isAt_projection c)
  obtain ⟨E, hE, himg⟩ := BlowupExceptional.exists_minusOne_of_literal hA b x hb hT hS'
  -- the fibre over `x` is exactly `E`
  have hfib : b.base ⁻¹' {x} = (E : Set S'.toScheme) := by
    have hirr := hb.pointFiber_isIrreducible (hT x) (T.closed_stalk_dimension_two x hx)
    let Wf : IrreducibleCloseds S'.toScheme := ⟨b.base ⁻¹' {x}, hirr, hx.preimage b.continuous⟩
    have hEW : (E : Set S'.toScheme) ⊆ Wf := by
      intro z hz
      have h := Set.mem_image_of_mem b.base hz
      rw [himg] at h
      exact h
    have hW : (Wf : Set S'.toScheme) ≠ Set.univ := by
      intro hW
      have hg : b.base (genericPoint S'.toScheme) = x := by
        have hmem : genericPoint S'.toScheme ∈ (Wf : Set S'.toScheme) := by
          rw [hW]
          trivial
        exact hmem
      exact T.closedPoint_ne_genericPoint x hx
        (hg.symm.trans hb.isBirationalScheme.map_genericPoint)
    exact (E.coe_eq_of_subset_irreducibleCloseds Wf hEW hW).symm
  exact ⟨S', b, E, hS', hb.isContraction_of_exceptionalFiber hT E hfib, hE, himg⟩

/-- **Theorem 4.6 in the interface form of Theorem 7.1**, given the Stacks 0AGQ literal and strict
transforms along contractions. -/
theorem isolatedExchangeHyp_of_literal {k : Type u} [Field k] [IsAlgClosed k]
    (hA : KltDP.Literature.Stacks.BlowupRegularPointLiteral k) (hL : HasContractionLifts k)
    (R : ResolutionDatum k) [DecidableRel R.graph.Adj] (p : ℕ) [CharP k p] (hp : 0 < p) :
    IsolatedExchangeHyp R :=
  isolatedExchangeHyp_of_blowups (hasPointBlowups_of_literal hA) hL R p hp

end KltDP.Manuscript.S04

#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.Aterm_mulVec_lamTm
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.terminal_gain_eq
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.anticanonicalContraction_terminal
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.card_components_famT
#print axioms KltDP.Manuscript.S04.IsolatedNodeExchange.exists_terminal_datum
#print axioms KltDP.Manuscript.S04.isolatedExchangeTerminalHyp_of_blowups
#print axioms KltDP.Manuscript.S04.isolatedExchangeHyp_of_blowups
#print axioms KltDP.Manuscript.S04.hasPointBlowups_of_literal
#print axioms KltDP.Manuscript.S04.isolatedExchangeHyp_of_literal
