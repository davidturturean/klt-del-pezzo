import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The `I`-adic order of a ring element, and the multiplicity at a closed point

BRIEF35 task 1, generalised in BRIEF36 task 2. For an ideal `I` of a commutative ring and `f : R`,
the largest `n` with `f ∈ I ^ n`. Specialised at `I = maximalIdeal R` this is the multiplicity at a
closed point that the F09 block has been missing.

## Why an arbitrary ideal and not only the maximal ideal

The original form fixed `I = maximalIdeal R`. That is the right invariant at a closed point of a
surface, but the one place it has to be *computed* — the Rees chart of a blowup — presents the plane
as the polynomial ring `k[u][v]`, which is **not local**; the centre is the maximal ideal `(u,v)` of
that global ring, and the accepted chart algebra is stated there. Transferring along
`IsLocalization.AtPrime` is not available: the accepted tree offers
`IsLocalization.AtPrime.to_map_mem_maximal_iff`, which is membership in the maximal ideal, not in its
powers, so the localisation route needs a lemma nobody has. Taking the order at an arbitrary ideal
directly avoids that transfer entirely, and costs nothing: every proof below was already ideal-generic
apart from where boundedness comes from.

## Why this definition, and why not Mathlib's

* **Not `multiplicity` / `emultiplicity`.** The pinned Mathlib's `emultiplicity a b` is the supremum of
  `n` with `a ^ n ∣ b` — divisibility by a ring *element*. The invariant needed here is membership in
  powers of an *ideal*, and in the intended application `R = O_{S,x}` is regular local of dimension
  two, where `m` is not principal. So `emultiplicity` is not applicable and cannot be reused for the
  definition. What *is* reused from Mathlib is Krull's intersection theorem for boundedness, and the
  ideal-power API.
* **Not the length of `R ⧸ (f)`.** That is a different invariant: it agrees with the order only in
  dimension one (for a DVR). In dimension two the length of `R ⧸ (f)` is infinite for `f` in a
  non-maximal prime, while the adic order is finite for every `f ≠ 0`. The strict-transform formula
  needs the order of vanishing of a local equation, which is the adic order.
* **Encoding: a supremum over `ℕ`, not `Nat.find` and not `ℕ∞`.** Membership in an ideal is not
  decidable, so a `Nat.find` encoding does not elaborate — Mathlib's own `emultiplicity` is
  `if h : FiniteMultiplicity a b then Nat.find h else ⊤` precisely to work around that. Taking
  `sSup {n : ℕ | f ∈ I ^ n}` in `ℕ` needs no decidability and no truncated subtraction: the set is
  nonempty (`I ^ 0 = ⊤`) and, under either boundedness hypothesis below, bounded above, so
  `Nat.sSup_mem` gives membership at the order itself and `le_csSup` / `csSup_le` give both directions
  of `le_adicOrder_iff_mem`.

**Junk value.** `sSup` of an unbounded set of naturals is `0` in Mathlib. For `f = 0`, or for `I = ⊤`,
the membership set is all of `ℕ`, so the order is the junk value `0`, not a real order. Every
substantive lemma below therefore carries an explicit boundedness hypothesis; nothing reads the order
of `0`.

## Boundedness, supplied two ways

The core API is stated from a bare `BddAbove (powMemSet I f)` hypothesis, and two suppliers discharge
it from Krull's intersection theorem:

* `bddAbove_powMemSet_of_isLocalRing` — Noetherian **local**, at the maximal ideal
  (`Ideal.iInf_pow_eq_bot_of_isLocalRing`). This is the closed-point case.
* `bddAbove_powMemSet_of_isDomain` — Noetherian **domain**, at any proper ideal
  (`Ideal.iInf_pow_eq_bot_of_isDomain`). This is the case the Rees chart needs, since `k[u][v]` is a
  Noetherian domain and the centre `(u,v)` is maximal, hence proper.

## What is proved

* `exists_not_mem_pow_of_iInf`, `bddAbove_powMemSet_of_exists` and the two suppliers — **finiteness**.
* `mem_pow_adicOrder`, `not_mem_pow_succ`, **`le_adicOrder_iff_mem`** — the defining characterisation.
* `one_le_adicOrder_iff_mem` — **positivity**, generically; `one_le_localAdicOrder_iff_nonunit` is its
  closed-point form, where lying in the maximal ideal is being a nonunit.
* `mem_pow_add_of_mem_of_mem`, **`add_le_adicOrder_mul`** — **superadditivity**
  `ord f + ord g ≤ ord (f * g)`.

## The additivity gap

Equality `ord (f * g) = ord f + ord g` holds when the associated graded ring `⊕ I^n / I^{n+1}` is a
domain (the initial forms multiply). **It is not stateable in the pinned Mathlib**: that Mathlib has
`Ideal.Filtration` but no associated-graded construction, so the hypothesis itself cannot be written
down. Rather than half-state it, the property is recorded as the named `Prop` `HasAdditiveAdicOrder`,
so consumers carry it explicitly and it can be discharged once an associated-graded construction
exists. Nothing below assumes it; `add_le_adicOrder_mul` gives the inequality unconditionally.
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.RingTheory.LocalAdicOrder

variable {R : Type u} [CommRing R]

/-! ## Definition, at an arbitrary ideal -/

/-- The set of exponents `n` with `f ∈ I ^ n`. -/
def powMemSet (I : Ideal R) (f : R) : Set ℕ := {n : ℕ | f ∈ I ^ n}

theorem mem_powMemSet_iff (I : Ideal R) (f : R) (n : ℕ) :
    n ∈ powMemSet I f ↔ f ∈ I ^ n := Iff.rfl

/-- **The `I`-adic order of `f`**: the largest `n` with `f ∈ I ^ n`. When the exponent set is
unbounded this is Mathlib's junk value `0`; every substantive lemma assumes boundedness. -/
def adicOrder (I : Ideal R) (f : R) : ℕ := sSup (powMemSet I f)

/-- Every element lies in the zeroth power, which is the whole ring. -/
theorem mem_pow_zero (I : Ideal R) (f : R) : f ∈ I ^ 0 := by
  rw [pow_zero, Ideal.one_eq_top]
  trivial

theorem powMemSet_nonempty (I : Ideal R) (f : R) : (powMemSet I f).Nonempty :=
  ⟨0, mem_pow_zero I f⟩

/-- The exponent set is downward closed. -/
theorem powMemSet_downward {I : Ideal R} {f : R} {m n : ℕ} (hmn : m ≤ n)
    (hn : n ∈ powMemSet I f) : m ∈ powMemSet I f :=
  Ideal.pow_le_pow_right hmn hn

/-! ## Finiteness, by Krull intersection -/

section Bounded

variable {I : Ideal R} {f : R}

/-- Escaping one power bounds the exponent set. -/
theorem bddAbove_powMemSet_of_exists (h : ∃ n : ℕ, f ∉ I ^ n) : BddAbove (powMemSet I f) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hN (powMemSet_downward hlt.le hn)

/-- A nonzero element escapes some power whenever the powers intersect in zero. -/
theorem exists_not_mem_pow_of_iInf (hbot : ⨅ n : ℕ, I ^ n = ⊥) (hf : f ≠ 0) :
    ∃ n : ℕ, f ∉ I ^ n := by
  by_contra h
  push_neg at h
  apply hf
  have hmem : f ∈ ⨅ n : ℕ, I ^ n := (Submodule.mem_iInf _).mpr h
  rw [hbot] at hmem
  exact Ideal.mem_bot.mp hmem

/-- **Finiteness at a closed point**: Noetherian local, at the maximal ideal. -/
theorem bddAbove_powMemSet_of_isLocalRing [IsNoetherianRing R] [IsLocalRing R] (hf : f ≠ 0) :
    BddAbove (powMemSet (maximalIdeal R) f) :=
  bddAbove_powMemSet_of_exists
    (exists_not_mem_pow_of_iInf
      (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top) hf)

/-- **Finiteness on a Noetherian domain**, at any proper ideal. This is the form the Rees chart needs:
the polynomial plane is a Noetherian domain and the blowup centre is a maximal, hence proper, ideal. -/
theorem bddAbove_powMemSet_of_isDomain [IsNoetherianRing R] [IsDomain R] (hI : I ≠ ⊤) (hf : f ≠ 0) :
    BddAbove (powMemSet I f) :=
  bddAbove_powMemSet_of_exists
    (exists_not_mem_pow_of_iInf (Ideal.iInf_pow_eq_bot_of_isDomain I hI) hf)

/-! ## The defining characterisation -/

/-- `f` lies in the power given by its order. -/
theorem mem_pow_adicOrder (hbdd : BddAbove (powMemSet I f)) : f ∈ I ^ adicOrder I f :=
  Nat.sSup_mem (powMemSet_nonempty I f) hbdd

/-- **The characterisation of the order**: `n ≤ ord f` exactly when `f ∈ I ^ n`. -/
theorem le_adicOrder_iff_mem (hbdd : BddAbove (powMemSet I f)) (n : ℕ) :
    n ≤ adicOrder I f ↔ f ∈ I ^ n := by
  constructor
  · intro hn
    exact powMemSet_downward hn (mem_pow_adicOrder hbdd)
  · intro hmem
    exact le_csSup hbdd hmem

/-- `f` does not lie in the next power. -/
theorem not_mem_pow_succ (hbdd : BddAbove (powMemSet I f)) : f ∉ I ^ (adicOrder I f + 1) := by
  intro hmem
  have hle : adicOrder I f + 1 ≤ adicOrder I f := (le_adicOrder_iff_mem hbdd _).mpr hmem
  omega

/-- The order is the largest exponent: any bound on the exponent set bounds the order. -/
theorem adicOrder_le_of_forall {a : ℕ} (h : ∀ n ∈ powMemSet I f, n ≤ a) : adicOrder I f ≤ a :=
  csSup_le (powMemSet_nonempty I f) h

/-- **Positivity**, generically: the order is at least one exactly when `f` lies in the ideal. -/
theorem one_le_adicOrder_iff_mem (hbdd : BddAbove (powMemSet I f)) :
    1 ≤ adicOrder I f ↔ f ∈ I := by
  rw [le_adicOrder_iff_mem hbdd, pow_one]

end Bounded

/-! ## Superadditivity -/

/-- Products land in the sum of the powers. -/
theorem mem_pow_add_of_mem_of_mem {I : Ideal R} {f g : R} {a b : ℕ} (hf : f ∈ I ^ a)
    (hg : g ∈ I ^ b) : f * g ∈ I ^ (a + b) := by
  exact pow_add I a b ▸ Ideal.mul_mem_mul hf hg

/-- **Superadditivity**: `ord f + ord g ≤ ord (f * g)`. Equality needs the associated graded ring to be
a domain, which the pinned Mathlib cannot express — see `HasAdditiveAdicOrder`. -/
theorem add_le_adicOrder_mul {I : Ideal R} {f g : R} (hf : BddAbove (powMemSet I f))
    (hg : BddAbove (powMemSet I g)) (hfg : BddAbove (powMemSet I (f * g))) :
    adicOrder I f + adicOrder I g ≤ adicOrder I (f * g) := by
  rw [le_adicOrder_iff_mem hfg]
  exact mem_pow_add_of_mem_of_mem (mem_pow_adicOrder hf) (mem_pow_adicOrder hg)

/-- Superadditivity on a Noetherian domain, with boundedness discharged. -/
theorem add_le_adicOrder_mul_of_isDomain [IsNoetherianRing R] [IsDomain R] {I : Ideal R}
    (hI : I ≠ ⊤) {f g : R} (hf : f ≠ 0) (hg : g ≠ 0) :
    adicOrder I f + adicOrder I g ≤ adicOrder I (f * g) :=
  add_le_adicOrder_mul (bddAbove_powMemSet_of_isDomain hI hf)
    (bddAbove_powMemSet_of_isDomain hI hg)
    (bddAbove_powMemSet_of_isDomain hI (mul_ne_zero hf hg))

/-! ## The closed-point case -/

section LocalRing

variable [IsLocalRing R]

/-- **The multiplicity of `f` at the closed point**: the `m`-adic order. -/
abbrev localAdicOrder (f : R) : ℕ := adicOrder (maximalIdeal R) f

/-- **Positivity at a closed point**: for a nonzero element the multiplicity is at least one exactly
for the nonunits. -/
theorem one_le_localAdicOrder_iff_nonunit [IsNoetherianRing R] {f : R} (hf : f ≠ 0) :
    1 ≤ localAdicOrder f ↔ ¬ IsUnit f := by
  rw [one_le_adicOrder_iff_mem (bddAbove_powMemSet_of_isLocalRing hf)]
  exact (mem_maximalIdeal f).trans mem_nonunits_iff

end LocalRing

/-! ## The additivity gap, as a named hypothesis -/

/-- The `I`-adic order is additive on nonzero elements. This holds when the associated graded ring
`⊕ I^n / I^{n+1}` is a domain, which the pinned Mathlib cannot state (it has `Ideal.Filtration` but no
associated-graded construction). Recorded as a named `Prop` so consumers can carry it explicitly;
nothing in this module assumes it, and `add_le_adicOrder_mul` gives the inequality unconditionally. -/
def HasAdditiveAdicOrder (I : Ideal R) : Prop :=
  ∀ f g : R, f ≠ 0 → g ≠ 0 → adicOrder I (f * g) = adicOrder I f + adicOrder I g

theorem adicOrder_mul_of_additive {I : Ideal R} (h : HasAdditiveAdicOrder I) {f g : R}
    (hf : f ≠ 0) (hg : g ≠ 0) : adicOrder I (f * g) = adicOrder I f + adicOrder I g := h f g hf hg

end KltDP.RingTheory.LocalAdicOrder
