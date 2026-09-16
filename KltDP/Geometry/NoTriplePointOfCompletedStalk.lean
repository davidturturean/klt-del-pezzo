import KltDP.Geometry.TransverseBranchesOfCompletedStalkUnconditional
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# No triple points from the completed-stalk node model

BRIEF28, task 1: a point of a reduced Noetherian scheme over `k` whose completed local ring is
`k⟦x, y⟧ ⧸ (x y)` lies on at most two irreducible components, and hence the completed-stalk form of
nodality alone (no separate no-triple-point hypothesis) gives transverse component branches.

**Primes of the model** (`k⟦x, y⟧ ⧸ (x y)`, namespace `KltDP.RingTheory.OrdinaryDoublePointModel`):
every prime contains `x̄` or `ȳ` (`x̄ ȳ = 0`); a prime containing `x̄ᵢ` but not `x̄ⱼ` equals `(x̄ᵢ)`
(`eq_span_xBar_of_not_mem`: its image under the surjective axis evaluation `evM j`, whose kernel is
`(x̄ᵢ)`, is a prime of the discrete valuation ring `k⟦X⟧` avoiding `X = evM j x̄ⱼ`, hence zero); a prime
containing both is the maximal ideal (`eq_maximalIdeal_of_mem_of_ne`). Consequently two primes containing
the same `x̄ᵢ` are comparable (`le_or_le_of_xBar_mem`) and **among any three primes of the model two are
comparable** (`exists_le_of_three`, pigeonhole on `x̄`, `ȳ`).

**Going down** (namespace `KltDP.RingTheory.NodalCompletion`): for a Noetherian local ring `O`, the
completion `Ô` is flat over `O` (Mathlib's `AdicCompletion.flat_of_isNoetherian`), so `O → Ô` has going
down (`Algebra.HasGoingDown.of_flat`); since `m̂` lies over `m` (BRIEF26's `algebraMap_mem_maximalIdeal_iff`),
**every prime of `O` is the contraction of a prime of `Ô`** (`exists_isPrime_comap_eq`).

**Scheme part** (namespace `KltDP.Geometry.RationalTreePicard`): three pairwise distinct components
through `q` have pairwise incomparable prime stalk ideals (BRIEF27's `eq_of_stalkIdeal_le`); their
contractions from `Ô_{X, q} ≃ k⟦x, y⟧ ⧸ (x y)` would be three pairwise incomparable primes of the model —
impossible. Hence `eq_or_eq_or_eq_of_completedStalk` (at most two components through a point with the
node model), `no_triple_point_of_completedStalk` (the hypothesis `hno` of BRIEF27's assembly, derived from
the isomorphisms), and **`hasTransverseComponentBranches_of_completedStalk'`**: completed-stalk
isomorphisms `Ô_{X, q} ≃ₐ[k] k⟦x, y⟧ ⧸ (x y)` at every point where a component meets the union of the
others imply `HasTransverseComponentBranches X`, with no further hypothesis.
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.RingTheory.OrdinaryDoublePointModel

open KltDP.Geometry.IntrinsicNodal

variable (k : Type u) [Field k]

/-! ## The prime ideals of `k⟦x, y⟧ ⧸ (x y)` -/

/-- The axis evaluation `k⟦x₀, x₁⟧ → k⟦X⟧` along `xᵢ` is surjective. -/
theorem ev_surjective (i : Fin 2) : Function.Surjective (ev k i) := by
  intro g
  refine ⟨fun m => if m = Finsupp.single i (m i) then PowerSeries.coeff k (m i) g else 0, ?_⟩
  refine PowerSeries.ext fun n => ?_
  rw [coeff_ev]
  show (if Finsupp.single i n = Finsupp.single i ((Finsupp.single i n) i) then
    PowerSeries.coeff k ((Finsupp.single i n) i) g else 0) = PowerSeries.coeff k n g
  rw [Finsupp.single_eq_same, if_pos rfl]

theorem evM_surjective (i : Fin 2) : Function.Surjective (evM k i) := by
  intro g
  obtain ⟨φ, rfl⟩ := ev_surjective k i g
  exact ⟨Ideal.Quotient.mk _ φ, evM_mk k i φ⟩

theorem ev_X_self (i : Fin 2) : ev k i (MvPowerSeries.X i : PS k) = PowerSeries.X := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_ev, MvPowerSeries.coeff_X, PowerSeries.coeff_X]
  simp only [(Finsupp.single_injective i).eq_iff]

theorem evM_xBar_self (i : Fin 2) :
    evM k i (xBar k i : ordinaryDoublePointModel k) = PowerSeries.X := by
  rw [xBar_val, evM_mk, ev_X_self]

theorem ker_evM_one :
    RingHom.ker (evM k 1) = Ideal.span {(xBar k 0 : ordinaryDoublePointModel k)} := by
  ext z
  rw [RingHom.mem_ker, mem_span_xBar_zero_iff]

theorem ker_evM_zero :
    RingHom.ker (evM k 0) = Ideal.span {(xBar k 1 : ordinaryDoublePointModel k)} := by
  ext z
  rw [RingHom.mem_ker, mem_span_xBar_one_iff]

theorem ker_evM_of_ne {i j : Fin 2} (hij : i ≠ j) :
    RingHom.ker (evM k j) = Ideal.span {(xBar k i : ordinaryDoublePointModel k)} := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ker_evM_one k
  · exact ker_evM_zero k
  · exact absurd rfl hij

/-- Every prime of the model contains `x̄` or `ȳ`. -/
theorem xBar_mem_or_xBar_mem (Q : Ideal (ordinaryDoublePointModel k)) [Q.IsPrime] :
    (xBar k 0 : ordinaryDoublePointModel k) ∈ Q ∨ (xBar k 1 : ordinaryDoublePointModel k) ∈ Q :=
  Ideal.IsPrime.mem_or_mem ‹_› (by rw [xBar_mul_xBar]; exact Q.zero_mem)

/-- A prime of the model containing `x̄ᵢ` but not `x̄ⱼ` (`i ≠ j`) is `(x̄ᵢ)`: its image under the axis
evaluation `evM j` (kernel `(x̄ᵢ)`) is a prime of the discrete valuation ring `k⟦X⟧` not containing
`X = evM j x̄ⱼ`, hence zero. -/
theorem eq_span_xBar_of_not_mem (Q : Ideal (ordinaryDoublePointModel k)) [Q.IsPrime] {i j : Fin 2}
    (hij : i ≠ j) (hi : (xBar k i : ordinaryDoublePointModel k) ∈ Q)
    (hj : (xBar k j : ordinaryDoublePointModel k) ∉ Q) :
    Q = Ideal.span {(xBar k i : ordinaryDoublePointModel k)} := by
  have hker : RingHom.ker (evM k j) = Ideal.span {(xBar k i : ordinaryDoublePointModel k)} :=
    ker_evM_of_ne k hij
  have hle : Ideal.span {(xBar k i : ordinaryDoublePointModel k)} ≤ Q :=
    (Ideal.span_singleton_le_iff_mem _).mpr hi
  have hkerQ : RingHom.ker (evM k j) ≤ Q := hker ▸ hle
  haveI hQ' : (Q.map (evM k j)).IsPrime :=
    Ideal.map_isPrime_of_surjective (evM_surjective k j) hkerQ
  have hbot : Q.map (evM k j) = ⊥ := by
    by_contra hne
    have hmax : (Q.map (evM k j)).IsMaximal := IsPrime.to_maximal_ideal hne
    have hX : (PowerSeries.X : PowerSeries k) ∈ Q.map (evM k j) := by
      rw [IsLocalRing.eq_maximalIdeal hmax, PowerSeries.maximalIdeal_eq_span_X]
      exact Ideal.mem_span_singleton_self _
    apply hj
    have h1 : (xBar k j : ordinaryDoublePointModel k) ∈
        Ideal.comap (evM k j) (Q.map (evM k j)) := by
      rw [Ideal.mem_comap, evM_xBar_self]
      exact hX
    rwa [Ideal.comap_map_of_surjective _ (evM_surjective k j), ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerQ] at h1
  refine le_antisymm (fun z hz => ?_) hle
  rw [← hker, RingHom.mem_ker, ← Ideal.mem_bot, ← hbot]
  exact Ideal.mem_map_of_mem _ hz

/-- A prime of the model containing `x̄` and `ȳ` is the maximal ideal. -/
theorem eq_maximalIdeal_of_mem (Q : Ideal (ordinaryDoublePointModel k)) [Q.IsPrime]
    (h0 : (xBar k 0 : ordinaryDoublePointModel k) ∈ Q)
    (h1 : (xBar k 1 : ordinaryDoublePointModel k) ∈ Q) :
    Q = maximalIdeal (ordinaryDoublePointModel k) := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) fun z hz => ?_
  obtain ⟨a, b, rfl⟩ := exists_eq_mul_xBar_add k hz
  exact Q.add_mem (Q.mul_mem_left a h0) (Q.mul_mem_left b h1)

theorem eq_maximalIdeal_of_mem_of_ne (Q : Ideal (ordinaryDoublePointModel k)) [Q.IsPrime]
    {i j : Fin 2} (hij : i ≠ j) (hi : (xBar k i : ordinaryDoublePointModel k) ∈ Q)
    (hj : (xBar k j : ordinaryDoublePointModel k) ∈ Q) :
    Q = maximalIdeal (ordinaryDoublePointModel k) := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact eq_maximalIdeal_of_mem k Q hi hj
  · exact eq_maximalIdeal_of_mem k Q hj hi
  · exact absurd rfl hij

/-- Two primes of the model containing the same `x̄ᵢ` are comparable: each is `(x̄ᵢ)` or the maximal
ideal. -/
theorem le_or_le_of_xBar_mem (Q₁ Q₂ : Ideal (ordinaryDoublePointModel k)) [Q₁.IsPrime] [Q₂.IsPrime]
    {i j : Fin 2} (hij : i ≠ j) (h₁ : (xBar k i : ordinaryDoublePointModel k) ∈ Q₁)
    (h₂ : (xBar k i : ordinaryDoublePointModel k) ∈ Q₂) : Q₁ ≤ Q₂ ∨ Q₂ ≤ Q₁ := by
  by_cases hj₁ : (xBar k j : ordinaryDoublePointModel k) ∈ Q₁ <;>
    by_cases hj₂ : (xBar k j : ordinaryDoublePointModel k) ∈ Q₂
  · left
    rw [eq_maximalIdeal_of_mem_of_ne k Q₁ hij h₁ hj₁, eq_maximalIdeal_of_mem_of_ne k Q₂ hij h₂ hj₂]
  · right
    rw [eq_span_xBar_of_not_mem k Q₂ hij h₂ hj₂]
    exact (Ideal.span_singleton_le_iff_mem _).mpr h₁
  · left
    rw [eq_span_xBar_of_not_mem k Q₁ hij h₁ hj₁]
    exact (Ideal.span_singleton_le_iff_mem _).mpr h₂
  · left
    rw [eq_span_xBar_of_not_mem k Q₁ hij h₁ hj₁, eq_span_xBar_of_not_mem k Q₂ hij h₂ hj₂]

/-- **Among any three primes of `k⟦x, y⟧ ⧸ (x y)` two are comparable** (the primes are `(x̄)`, `(ȳ)` and
the maximal ideal). -/
theorem exists_le_of_three (Q₁ Q₂ Q₃ : Ideal (ordinaryDoublePointModel k)) [Q₁.IsPrime] [Q₂.IsPrime]
    [Q₃.IsPrime] :
    (Q₁ ≤ Q₂ ∨ Q₂ ≤ Q₁) ∨ (Q₁ ≤ Q₃ ∨ Q₃ ≤ Q₁) ∨ (Q₂ ≤ Q₃ ∨ Q₃ ≤ Q₂) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rcases xBar_mem_or_xBar_mem k Q₁ with h₁ | h₁ <;>
    rcases xBar_mem_or_xBar_mem k Q₂ with h₂ | h₂ <;>
    rcases xBar_mem_or_xBar_mem k Q₃ with h₃ | h₃
  · exact Or.inl (le_or_le_of_xBar_mem k Q₁ Q₂ h01 h₁ h₂)
  · exact Or.inl (le_or_le_of_xBar_mem k Q₁ Q₂ h01 h₁ h₂)
  · exact Or.inr (Or.inl (le_or_le_of_xBar_mem k Q₁ Q₃ h01 h₁ h₃))
  · exact Or.inr (Or.inr (le_or_le_of_xBar_mem k Q₂ Q₃ h10 h₂ h₃))
  · exact Or.inr (Or.inr (le_or_le_of_xBar_mem k Q₂ Q₃ h01 h₂ h₃))
  · exact Or.inr (Or.inl (le_or_le_of_xBar_mem k Q₁ Q₃ h10 h₁ h₃))
  · exact Or.inl (le_or_le_of_xBar_mem k Q₁ Q₂ h10 h₁ h₂)
  · exact Or.inl (le_or_le_of_xBar_mem k Q₁ Q₂ h10 h₁ h₂)

end KltDP.RingTheory.OrdinaryDoublePointModel

namespace KltDP.RingTheory.NodalCompletion

open KltDP.RingTheory.AdicCompletionKernelEval

variable {O : Type u} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]

local instance compl_isLocalRing_goingDown : IsLocalRing (Compl O) :=
  isLocalRing_adicCompletion (maximalIdeal O)

/-! ## Going down along `O → Ô` -/

/-- The maximal ideal of the completion lies over the maximal ideal. -/
theorem maximalIdeal_liesOver : (maximalIdeal (Compl O)).LiesOver (maximalIdeal O) :=
  ⟨by
    ext r
    exact (algebraMap_mem_maximalIdeal_iff r).symm⟩

/-- **Every prime of a Noetherian local ring is the contraction of a prime of its completion**: going
down for the flat map `O → Ô` (Mathlib's `Algebra.HasGoingDown.of_flat`), applied from `m̂` over `m`. -/
theorem exists_isPrime_comap_eq (P : Ideal O) [P.IsPrime] :
    ∃ Q : Ideal (Compl O), Q.IsPrime ∧ Ideal.comap (algebraMap O (Compl O)) Q = P := by
  haveI := maximalIdeal_liesOver (O := O)
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P) (q := maximalIdeal O)
    (maximalIdeal (Compl O)) (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
  exact ⟨Q, hQ, hQP.over.symm⟩

end KltDP.RingTheory.NodalCompletion

namespace KltDP.Geometry.RationalTreePicard

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.IntrinsicNodal KltDP.RingTheory.OrdinaryDoublePointModel

variable {k : Type u} [Field k] (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of k))

/-! ## At most two components through a point with the node model -/

omit [NoetherianSpace X] [IsLocallyNoetherian X] in
/-- Every point of a scheme lies in an affine open. -/
theorem exists_mem_affineOpens (q : X) : ∃ U : X.affineOpens, q ∈ U.1 := by
  obtain ⟨U, hU, hqU, -⟩ :=
    (Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_affine_open X)) (Opens.mem_top q)
  exact ⟨⟨U, hU⟩, hqU⟩

omit [IsLocallyNoetherian X] in
/-- Components whose stalk ideals are contractions of comparable ideals of the completed stalk
coincide. -/
theorem eq_of_comap_le_comap (A B : ↥(irreducibleComponents X)) (U : X.affineOpens) {q : X}
    (hq : q ∈ U.1) (hqB : q ∈ B.1) (QA QB : Ideal (completedStalk X q))
    (hA : Ideal.comap (algebraMap (X.presheaf.stalk q) (completedStalk X q)) QA =
      stalkIdeal {A} U hq)
    (hB : Ideal.comap (algebraMap (X.presheaf.stalk q) (completedStalk X q)) QB =
      stalkIdeal {B} U hq)
    (h : QA ≤ QB) : A = B := by
  refine eq_of_stalkIdeal_le A B U hq hqB ?_
  rw [← hA, ← hB]
  exact Ideal.comap_mono h

/-- **At most two irreducible components pass through a point whose completed local ring is
`k⟦x, y⟧ ⧸ (x y)`.** -/
theorem eq_or_eq_or_eq_of_completedStalk (C D E : ↥(irreducibleComponents X)) (q : X)
    (hqC : q ∈ C.1) (hqD : q ∈ D.1) (hqE : q ∈ E.1)
    (e : letI := stalkAlgebra f q; completedStalk X q ≃ₐ[k] ordinaryDoublePointModel k) :
    C = D ∨ C = E ∨ D = E := by
  obtain ⟨U, hq⟩ := exists_mem_affineOpens X q
  letI := stalkAlgebra f q
  haveI : IsNoetherianRing (X.presheaf.stalk q) :=
    KltDP.Geometry.isNoetherianRing_stalk_of_isLocallyNoetherian X q
  haveI hPC : (stalkIdeal {C} U hq).IsPrime := stalkIdeal_singleton_isPrime C U hq hqC
  haveI hPD : (stalkIdeal {D} U hq).IsPrime := stalkIdeal_singleton_isPrime D U hq hqD
  haveI hPE : (stalkIdeal {E} U hq).IsPrime := stalkIdeal_singleton_isPrime E U hq hqE
  obtain ⟨QC, hQC, hC⟩ :=
    KltDP.RingTheory.NodalCompletion.exists_isPrime_comap_eq (stalkIdeal {C} U hq)
  obtain ⟨QD, hQD, hD⟩ :=
    KltDP.RingTheory.NodalCompletion.exists_isPrime_comap_eq (stalkIdeal {D} U hq)
  obtain ⟨QE, hQE, hE⟩ :=
    KltDP.RingTheory.NodalCompletion.exists_isPrime_comap_eq (stalkIdeal {E} U hq)
  haveI := hQC
  haveI := hQD
  haveI := hQE
  have hsurj : Function.Surjective e.symm.toRingHom := e.symm.surjective
  have hle : ∀ (A B : ↥(irreducibleComponents X)) (QA QB : Ideal (completedStalk X q)), q ∈ B.1 →
      Ideal.comap (algebraMap (X.presheaf.stalk q) (completedStalk X q)) QA = stalkIdeal {A} U hq →
      Ideal.comap (algebraMap (X.presheaf.stalk q) (completedStalk X q)) QB = stalkIdeal {B} U hq →
      Ideal.comap e.symm.toRingHom QA ≤ Ideal.comap e.symm.toRingHom QB → A = B := by
    intro A B QA QB hqB hA hB h
    exact eq_of_comap_le_comap X A B U hq hqB QA QB hA hB
      ((Ideal.comap_le_comap_iff_of_surjective _ hsurj _ _).mp h)
  rcases exists_le_of_three k (Ideal.comap e.symm.toRingHom QC) (Ideal.comap e.symm.toRingHom QD)
    (Ideal.comap e.symm.toRingHom QE) with (h | h) | (h | h) | (h | h)
  · exact Or.inl (hle C D QC QD hqD hC hD h)
  · exact Or.inl (hle D C QD QC hqC hD hC h).symm
  · exact Or.inr (Or.inl (hle C E QC QE hqE hC hE h))
  · exact Or.inr (Or.inl (hle E C QE QC hqC hE hC h).symm)
  · exact Or.inr (Or.inr (hle D E QD QE hqE hD hE h))
  · exact Or.inr (Or.inr (hle E D QE QD hqD hE hD h).symm)

/-- **The no-triple-point hypothesis of BRIEF27's assembly follows from the completed-stalk
isomorphisms** at the points where a component meets the union of the other components. -/
theorem no_triple_point_of_completedStalk
    (e : ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
      q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) →
      (letI := stalkAlgebra f q; completedStalk X q ≃ₐ[k] ordinaryDoublePointModel k))
    (C D E : ↥(irreducibleComponents X)) (q : X) (hqC : q ∈ C.1) (hqD : q ∈ D.1) (hqE : q ∈ E.1) :
    C = D ∨ C = E ∨ D = E := by
  by_cases hCD : C = D
  · exact Or.inl hCD
  · have hqCc : q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) :=
      (mem_componentClosedUnion X _ q).mpr
        ⟨D, fun h => hCD (Set.mem_singleton_iff.mp h).symm, hqD⟩
    exact eq_or_eq_or_eq_of_completedStalk X f C D E q hqC hqD hqE (e C q hqC hqCc)

/-- **Transverse component branches from the completed-stalk node model, with the isomorphisms as the
only hypothesis**: a reduced Noetherian, locally Noetherian scheme over `k` whose completed local ring
at every point where a component meets the union of the others is `k⟦x, y⟧ ⧸ (x y)` has transverse
component branches (the nodality hypothesis of `lem:tree-picard`). -/
theorem hasTransverseComponentBranches_of_completedStalk' [AlgebraicGeometry.IsReduced X]
    (e : ∀ (C : ↥(irreducibleComponents X)) (q : X), q ∈ C.1 →
      q ∈ (componentClosedUnion X ({C}ᶜ) : Set X) →
      (letI := stalkAlgebra f q; completedStalk X q ≃ₐ[k] ordinaryDoublePointModel k)) :
    HasTransverseComponentBranches X :=
  hasTransverseComponentBranches_of_completedStalk X f (no_triple_point_of_completedStalk X f e) e

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] (X₀ : Scheme.{0}) [NoetherianSpace X₀] [IsLocallyNoetherian X₀]
    [AlgebraicGeometry.IsReduced X₀] (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀))
    (e : ∀ (C : ↥(irreducibleComponents X₀)) (q : X₀), q ∈ C.1 →
      q ∈ (componentClosedUnion X₀ ({C}ᶜ) : Set X₀) →
      (letI := stalkAlgebra f₀ q; completedStalk X₀ q ≃ₐ[k₀] ordinaryDoublePointModel k₀)) :
    HasTransverseComponentBranches X₀ :=
  hasTransverseComponentBranches_of_completedStalk' X₀ f₀ e

end KltDP.Geometry.RationalTreePicard
