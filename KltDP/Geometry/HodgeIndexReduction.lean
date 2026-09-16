import KltDP.Geometry.NumericalSpaceRank

/-!
# The Hodge index theorem, reduced to one geometric hypothesis (F06)

The index theorem is not proved here and nothing is admitted. What is proved is the **reduction**: the
whole theorem follows from a single named geometric input, so consumers stop treating it as an opaque
parameter and the one genuinely missing fact becomes visible.

* **HI-3, the geometric core**, carried as the named hypothesis `HodgeIndexSemidefinite X hregular h`:
  the pairing is negative *semi*-definite on the orthogonal complement of a class `h` of positive
  square. This is what the classical proof extracts from surface Riemann–Roch, Serre duality and
  ampleness — all three absent from the accepted tree and from the pinned Mathlib (surface RR is not in
  Stacks and its planning source is unadmitted; Stacks 0FVZ needs Cohen–Macaulay, and "normal of
  dimension two ⇒ CM" is Serre's criterion, absent; `IsAmple` is not declared anywhere).
* **HI-1**, the linear algebra, is the pattern of `KltDP.Support.NegativeDefinite`, run here directly
  over `ℤ` — where it is *easier* than over a field, because no division is needed: a vector of zero
  square is orthogonal to the complement by choosing the integer `t = (|q·q| + 1) · sign (p·q)`.
* **HI-2**, non-degeneracy, is free: `NumericallyTrivial p` is by definition
  `∀ C, C.picardRestrictionDegree p = 0`, and pairing against the prime-curve class
  `[O_X(D_C)]` *is* that restriction degree.

**No literal enters.** `intersectionPairing` is an unconditional symmetric `ℤ`-bilinear form
(`intersectionPairing_add_left/_add_right/_neg_*`, and `intersectionPairing_symm` through E7's
unconditionally discharged `PrimeCurveIntersectionSymmetric`), and `picardPairing` inherits this. The
undischarged `NumericalIntersectionPolynomialLiteral` is needed only to identify this pairing with the
accepted `cartierEulerPairing`, which this module never does. Stating the index theorem over
`intersectionPairing`/`picardPairing` therefore avoids the literal entirely.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-! ### The pairing against a prime-curve class is the restriction degree -/

/-- **The bridge to numerical equivalence**: pairing with the class of `O_X(D_C)` is exactly the
restriction degree at `C` that `NumericallyTrivial` quantifies over. Unconditional. -/
theorem picardPairing_primeCurveClass (p : X.toScheme.Pic) (C : X.PrimeCurve) :
    picardPairing X hregular p
        (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C)) =
      C.picardRestrictionDegree p := by
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X.toScheme p
  rw [X.picardPairing_class hregular D (X.primeCurveCartier hregular C),
    X.intersectionPairing_primeCurveCartier hregular
      (X.primeCurveIntersectionSymmetric hregular) D C,
    C.intersectionNumber_eq_picardRestrictionDegree D]

/-- A class pairing to zero with every prime-curve class is numerically trivial. -/
theorem numericallyTrivial_of_pairing_primeCurveClass_eq_zero (p : X.toScheme.Pic)
    (h : ∀ C : X.PrimeCurve,
      picardPairing X hregular p
        (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C)) = 0) :
    X.NumericallyTrivial p := fun C =>
  (X.picardPairing_primeCurveClass hregular p C).symm.trans (h C)

/-! ### Integer powers: the pairing is `ℤ`-linear in each argument -/

/-- The pairing against a fixed class, as an additive homomorphism on `Additive Pic`. -/
def picardPairingHom (q : X.toScheme.Pic) : Additive X.toScheme.Pic →+ ℤ :=
  AddMonoidHom.mk' (fun p : Additive X.toScheme.Pic => picardPairing X hregular p.toMul q)
    (fun p p' => by
      simpa only [toMul_add] using
        X.picardPairing_mul_left_of_regular hregular p.toMul p'.toMul q)

@[simp]
theorem picardPairingHom_apply (q : X.toScheme.Pic) (p : Additive X.toScheme.Pic) :
    X.picardPairingHom hregular q p = picardPairing X hregular p.toMul q := rfl

/-- **`ℤ`-linearity in the first argument**: `(p ^ n) · q = n * (p · q)`. Proved through
`picardPairingHom`, exactly as lane A1's `infiniteOrder_of_degreeHom` does for an arbitrary
`Additive Pic →+ ℤ`. -/
theorem picardPairing_zpow_left (p q : X.toScheme.Pic) (n : ℤ) :
    picardPairing X hregular (p ^ n) q = n * picardPairing X hregular p q := by
  have h : X.picardPairingHom hregular q (Additive.ofMul (p ^ n)) =
      n • X.picardPairingHom hregular q (Additive.ofMul p) := by
    rw [ofMul_zpow, map_zsmul]
  simpa only [picardPairingHom_apply, toMul_ofMul, zsmul_eq_mul, smul_eq_mul] using h

/-- **`ℤ`-linearity in the second argument**, by symmetry. -/
theorem picardPairing_zpow_right (p q : X.toScheme.Pic) (n : ℤ) :
    picardPairing X hregular p (q ^ n) = n * picardPairing X hregular p q := by
  rw [X.picardPairing_symm hregular p (q ^ n), X.picardPairing_zpow_left hregular q p n,
    X.picardPairing_symm hregular q p]

/-! ### HI-3, the single geometric hypothesis -/

/-- **HI-3 (named geometric hypothesis).** The pairing is negative semi-definite on the orthogonal
complement of `h`. This is the content the classical proof obtains from Riemann–Roch, duality and
ampleness; it is assumed here, never proved, and it is the only geometric input of the theorem. -/
def HodgeIndexSemidefinite (h : X.toScheme.Pic) : Prop :=
  ∀ p : X.toScheme.Pic, picardPairing X hregular h p = 0 → picardPairing X hregular p p ≤ 0

/-! ### HI-1 over `ℤ`: the kernel step, with no division -/

/-- **Kernel step.** If `p` lies in `h^⊥` with `p · p = 0`, it pairs to zero with every other element
of `h^⊥`. Over `ℤ` the discriminant argument needs no division: `(t·p + q)²  = 2t(p·q) + q²` must stay
`≤ 0` for every integer `t`, which fails for `t = (|q²| + 1) · sign (p·q)` unless `p·q = 0`. -/
theorem pairing_eq_zero_of_self_eq_zero_int (hHI : HodgeIndexSemidefinite X hregular h)
    (p q : X.toScheme.Pic) (hp : picardPairing X hregular h p = 0)
    (hq : picardPairing X hregular h q = 0) (hp0 : picardPairing X hregular p p = 0) :
    picardPairing X hregular p q = 0 := by
  set c := picardPairing X hregular p q with hc
  set d := picardPairing X hregular q q with hd
  have hdle : d ≤ 0 := hHI q hq
  have hqp : picardPairing X hregular q p = c := by
    rw [hc, X.picardPairing_symm hregular q p]
  -- `set` introduces let-bound locals; make them opaque so `lt_trichotomy` needs no `Decidable`
  clear_value c d
  -- every integer combination `p ^ t * q` again lies in `h^⊥`
  have hmem : ∀ t : ℤ, picardPairing X hregular h (p ^ t * q) = 0 := by
    intro t
    rw [X.picardPairing_mul_right_of_regular hregular h (p ^ t) q, hq, add_zero,
      X.picardPairing_zpow_right hregular h p t, hp, mul_zero]
  have hexp : ∀ t : ℤ, picardPairing X hregular (p ^ t * q) (p ^ t * q) = 2 * t * c + d := by
    intro t
    rw [X.picardPairing_mul_left_of_regular hregular (p ^ t) q (p ^ t * q),
      X.picardPairing_mul_right_of_regular hregular (p ^ t) (p ^ t) q,
      X.picardPairing_mul_right_of_regular hregular q (p ^ t) q,
      X.picardPairing_zpow_right hregular (p ^ t) p t,
      X.picardPairing_zpow_left hregular p p t,
      X.picardPairing_zpow_left hregular p q t,
      X.picardPairing_zpow_right hregular q p t, hp0, hqp, ← hc, ← hd]
    ring
  -- `rcases` first: after `by_contra` the trichotomy would be asked to eliminate into `Decidable`.
  -- The witness `1 - d` is positive because `d ≤ 0`, so no absolute value is needed.
  rcases lt_trichotomy c 0 with hneg | hzero | hpos
  · exfalso
    have hkey := hHI (p ^ (d - 1) * q) (hmem (d - 1))
    rw [hexp] at hkey
    have hprod : (0 : ℤ) ≤ (1 - d) * (-c - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hkey, hprod, hdle, hneg]
  · exact hzero
  · exfalso
    have hkey := hHI (p ^ (1 - d) * q) (hmem (1 - d))
    rw [hexp] at hkey
    have hprod : (0 : ℤ) ≤ (1 - d) * (c - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hkey, hprod, hdle, hpos]

/-! ### The reduction -/

/-- **The Hodge index theorem, reduced.** Given HI-3 and a class `h` of positive square, every class
orthogonal to `h` that is *not* numerically trivial has strictly negative square. The only geometric
input is `HodgeIndexSemidefinite`; nothing else is assumed and no literal enters. -/
theorem picardPairing_neg_of_orthogonal (h : X.toScheme.Pic)
    (hpos : 0 < picardPairing X hregular h h) (hHI : HodgeIndexSemidefinite X hregular h)
    (p : X.toScheme.Pic) (hperp : picardPairing X hregular h p = 0)
    (hnt : ¬ X.NumericallyTrivial p) :
    picardPairing X hregular p p < 0 := by
  rcases lt_or_eq_of_le (hHI p hperp) with hlt | heq
  · exact hlt
  refine absurd (X.numericallyTrivial_of_pairing_primeCurveClass_eq_zero hregular p ?_) hnt
  intro C
  set q := cartierPicardClass X.toScheme (X.primeCurveCartier hregular C) with hqdef
  -- `q' = q ^ (h·h) * h ^ (-(h·q))` lies in `h^⊥`
  set a := picardPairing X hregular h h with ha
  set b := picardPairing X hregular h q with hb
  have hq' : picardPairing X hregular h (q ^ a * h ^ (-b)) = 0 := by
    rw [X.picardPairing_mul_right_of_regular hregular h (q ^ a) (h ^ (-b)),
      X.picardPairing_zpow_right hregular h q a,
      X.picardPairing_zpow_right hregular h h (-b), ← ha, ← hb]
    ring
  have hpq' := X.pairing_eq_zero_of_self_eq_zero_int hregular hHI p (q ^ a * h ^ (-b))
    hperp hq' heq
  rw [X.picardPairing_mul_right_of_regular hregular p (q ^ a) (h ^ (-b)),
    X.picardPairing_zpow_right hregular p q a,
    X.picardPairing_zpow_right hregular p h (-b),
    X.picardPairing_symm hregular p h, hperp, mul_zero, add_zero] at hpq'
  rcases mul_eq_zero.mp hpq' with hA | hval
  · exact absurd (ha ▸ hA) (ne_of_gt hpos)
  · exact hval

/-! ### The signature statement -/

/-- **The Hodge index theorem in signature form**, as a named statement over the accepted numerical
quotient and E12's `picardRank`: there is a class of positive square, and the pairing is negative
definite on its orthogonal complement modulo numerical equivalence. Stated, not proved; its only
missing input is `HodgeIndexSemidefinite`. -/
def HodgeIndexSignature : Prop :=
  ∃ h : X.toScheme.Pic, 0 < picardPairing X hregular h h ∧
    HodgeIndexSemidefinite X hregular h

/-- **The index theorem from the signature statement.** -/
theorem hodgeIndex_of_signature (hsig : HodgeIndexSignature X hregular) :
    ∃ h : X.toScheme.Pic, 0 < picardPairing X hregular h h ∧
      ∀ p : X.toScheme.Pic, picardPairing X hregular h p = 0 →
        ¬ X.NumericallyTrivial p → picardPairing X hregular p p < 0 := by
  obtain ⟨h, hpos, hHI⟩ := hsig
  exact ⟨h, hpos, fun p hperp hnt =>
    X.picardPairing_neg_of_orthogonal hregular h hpos hHI p hperp hnt⟩

end KltDP.Geometry.NormalProjectiveSurface
