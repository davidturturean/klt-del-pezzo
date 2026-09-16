import KltDP.Geometry.AmpleSerre
import KltDP.Geometry.NumericalEquivalence
import KltDP.Geometry.FiniteTypeNoetherian

/-!
# Making `IsAmple` load-bearing: ample ⇒ semi-ample ⇒ nef, and the one geometric input

E28 defined `IsAmple` in Serre's original form and connected it to `IsSemiample`. This module
carries it the rest of the way into the positivity hierarchy, and states exactly where the
connection stops and why.

## Unconditional consequences of the definition

* `isAmple_of_toPic_eq` — ampleness depends only on the **Picard class**. The definition mentions
  `L` only through `L.toPic`, so two sheaves with the same class are ample together. This is what
  will let `isDelPezzo` be stated over `antiCanonicalClass` (E28), which is a class with no chosen
  representing sheaf.
* `isAmple_pow` — if `L` is ample and `M` has class `L^m` with `m > 0`, then `M` is ample: a twist
  by `M^n` is a twist by `L^(m·n)`, and `m·n ≥ n`, so the same bound `N` works.
* `picardRestrictionDegree_pow` — `C · (p^n) = n · (C · p)`, from the **accepted**
  `picardRestrictionDegreeHom` being an `AddMonoidHom` (`ofMul_pow`, `map_nsmul`). Absent before, by
  name and by shape sweep; the accepted tree uses the same idiom at `NumericalEquivalence:126`.

## The reduction, and the single geometric hypothesis

`GloballyGeneratedRestrictionNonneg` is the one input: *a globally generated invertible sheaf has
non-negative degree on every prime curve*. Given it, ampleness implies nefness outright:

* `isNef_of_isSemiample` — the core. Semi-ampleness gives `n > 0` and a sheaf of class `L^n` that is
  globally generated; the hypothesis makes its degree non-negative; `picardRestrictionDegree_pow`
  turns that into `0 ≤ n · (C · L)`, and `n > 0` gives `0 ≤ C · L`. Nefness is then the queued
  `isNef_iff_forall_primeCurve`.
* `isNef_of_isAmple` — the corollary, composing E28's `isSemiample_of_isAmple`. The
  `IsLocallyNoetherian` instance it needs is discharged from the **accepted**
  `NormalProjectiveSurface.isLocallyNoetherian`, not assumed.

This is the `HodgeIndexReduction`/HI-3 pattern: the geometric content is isolated at exactly one
named hypothesis, and everything else is proved.

**What would discharge `GloballyGeneratedRestrictionNonneg`**, precisely: pullback along
`C.inclusion` preserves epimorphisms (it is a left adjoint — accepted
`schemeModulePullbackPushforwardAdjunction`), so the restriction is globally generated on `C`; a
globally generated invertible sheaf on a nonempty curve has a nonzero global section; that section
gives an effective Cartier divisor by the accepted
`SectionEffectiveCartier.exists_effectiveCartier_of_nonzero_section`; and its degree is
non-negative by the accepted `lineDegree_cartier_eq_effectiveCartierDegree`, whose finiteness and
closed-point side conditions are the remaining work. Several compiles, not one — so it is named
here rather than attempted.

## The bigness implication remains to be formalized

On the intended integral projective surfaces, Serre's criterion characterizes ordinary ampleness,
which does imply ordinary bigness. This module does not formalize that growth argument.
`Positivity.IsBig` uses a positive rational coefficient in
`c · n^{dim X} ≤ h⁰(L^n)` for arbitrarily large `n`; allowing coefficients below one is essential,
as `O(1)` on the projective plane has `h⁰(O(n)) = (n+1)(n+2)/2`.

The former positive-natural coefficient was a definition error, not merely a missing geometric
proof. Correcting it does not supply the geometric comparison or the ampleness-to-growth theorem.
Such a proof could use a projective embedding and Hilbert-polynomial growth, or an appropriate
Riemann–Roch theorem with its hypotheses discharged. No such theorem is proved in this module.

Likewise nothing here witnesses ampleness: `IsAmple` still has no instance, and none is claimed.

Import closure is queue-internal (`AmpleSerre`, hence `Positivity`); the other two imports are
accepted. Nothing is admitted and no literature literal is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Geometry.AmplePositivity

open KltDP.Geometry.AmpleSerre KltDP.Geometry.NormalProjectiveSurface

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance amplePositivityMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

section Classes

variable {X : Scheme.{u}}

/-- **Ampleness depends only on the Picard class.** The definition mentions `L` only through
`L.toPic`. -/
theorem isAmple_of_toPic_eq {L L' : InvertibleSheaf X} (h : L.toPic = L'.toPic)
    (hL : IsAmple L) : IsAmple L' := by
  intro F hF
  obtain ⟨N, hN⟩ := hL F hF
  refine ⟨N, fun n hn => ?_⟩
  rw [← h]
  exact hN n hn

/-- **Ampleness passes to positive powers**: a twist by `M^n` is a twist by `L^(m*n)`, and
`m * n ≥ n`, so the bound from `L` serves for `M`. -/
theorem isAmple_pow {L M : InvertibleSheaf X} (m : ℕ) (hm : 0 < m)
    (hM : M.toPic = L.toPic ^ m) (h : IsAmple L) : IsAmple M := by
  intro F hF
  obtain ⟨N, hN⟩ := h F hF
  refine ⟨N, fun n hn => ?_⟩
  have hmn : n ≤ m * n := Nat.le_mul_of_pos_left n hm
  obtain ⟨P, hPclass, hPgg⟩ := hN (m * n) (le_trans hn hmn)
  refine ⟨P, ?_, hPgg⟩
  rw [hPclass, hM, ← pow_mul]

end Classes

section Surface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- **`C · (p^n) = n · (C · p)`**, from the accepted `picardRestrictionDegreeHom`. -/
theorem picardRestrictionDegree_pow (C : X.PrimeCurve) (p : X.toScheme.Pic) (n : ℕ) :
    C.picardRestrictionDegree (p ^ n) = n * C.picardRestrictionDegree p := by
  have h : X.picardRestrictionDegreeHom C (Additive.ofMul (p ^ n)) =
      n • X.picardRestrictionDegreeHom C (Additive.ofMul p) := by
    rw [ofMul_pow, map_nsmul]
  simpa only [picardRestrictionDegreeHom_apply, toMul_ofMul, nsmul_eq_mul] using h

/-- **The single geometric hypothesis.** A globally generated invertible sheaf has non-negative
degree on every prime curve. See the header for exactly which accepted results would discharge it;
it is assumed here, never proved, and it is the only geometric input below. -/
def GloballyGeneratedRestrictionNonneg : Prop :=
  ∀ M : InvertibleSheaf X.toScheme, Positivity.IsGloballyGenerated M.obj →
    ∀ C : X.PrimeCurve, 0 ≤ C.restrictionDegree M

/-- **Semi-ample implies nef**, given the one hypothesis. -/
theorem isNef_of_isSemiample (hGG : GloballyGeneratedRestrictionNonneg X)
    (L : InvertibleSheaf X.toScheme) (h : Positivity.IsSemiample L) :
    Positivity.IsNef X.structureMorphism L := by
  rw [Positivity.isNef_iff_forall_primeCurve]
  intro C
  obtain ⟨n, hn, M, hMclass, hMgg⟩ := h
  have h0 : 0 ≤ C.restrictionDegree M := hGG M hMgg C
  rw [← C.picardRestrictionDegree_toPic M, hMclass,
    picardRestrictionDegree_pow X C L.toPic n, C.picardRestrictionDegree_toPic] at h0
  by_contra hlt
  push_neg at hlt
  exact absurd h0 (not_le.mpr (mul_neg_of_pos_of_neg (by exact_mod_cast hn) hlt))

/-- **Ample implies nef.** The `IsLocallyNoetherian` instance that E28's `isSemiample_of_isAmple`
needs is discharged from the accepted `NormalProjectiveSurface.isLocallyNoetherian`. -/
theorem isNef_of_isAmple (hGG : GloballyGeneratedRestrictionNonneg X)
    (L : InvertibleSheaf X.toScheme) (h : IsAmple L) :
    Positivity.IsNef X.structureMorphism L := by
  letI := X.isLocallyNoetherian
  exact isNef_of_isSemiample X hGG L (isSemiample_of_isAmple L h)

end Surface

end KltDP.Geometry.AmplePositivity
