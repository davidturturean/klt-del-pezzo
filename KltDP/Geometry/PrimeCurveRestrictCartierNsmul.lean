import KltDP.Geometry.PrimeCurveRestrictCartierZero
import KltDP.Geometry.CartierDivisorPullbackAdd

/-!
# Natural multiples of the restriction of a Cartier divisor to a prime curve

The last law of the restriction functor `D ↦ D|_C` that the sibling pullback functor has and the
restriction does not: `pullbackDivisor_nsmul` is accepted, and with the accepted
`restrictCartier_add` together with the unit law `restrictCartier_zero` and the transport
`restrictCartier_congr` the same induction transfers line for line.

* `notInSupport_congr`, `intersectionDegree_congr` — transport of `NotInSupport` and of the
  intersection degree along an equality of divisors; `subst` then proof irrelevance, the shape of the
  accepted `pullbackDivisor_congr`;
* `notInSupport_nsmul` — a prime curve off the support of `D` is off the support of `n • D`, which is
  what makes the statement below typecheck at all;
* **`restrictCartier_nsmul`** — `(n • D)|_C = n • (D|_C)`;
* **`intersectionDegree_nsmul`** — `C · (n • D) = n * (C · D)` for the scheme-theoretic degree.

**Certification order (this module is not accepted-only).** Unlike `ModuleTensorInvertible`,
`CartierDivisorPullbackIdentity` and `PrimeCurveRestrictCartierZero`, whose closures are entirely
accepted, this module imports the **queued, not yet certified** `PrimeCurveRestrictCartierZero`
(for `restrictCartier_zero`, `restrictCartier_congr` and `notInSupport_zero`). It can therefore only
certify *after* that entry does. Its other import, `CartierDivisorPullbackAdd`, is accepted and
supplies the regular-equations witness `hasRegularCartierEquations_nsmul` for `n • D`; that namespace
is deliberately **not** opened, because its `hasRegularCartierEquations_add`/`_zero` are distinct
declarations sharing the bare names of the root-namespace ones used here.

Nothing is admitted and no literature literal is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)

/-- Transport of `C ⊄ Supp D` along an equality of divisors (the two proof arguments are `Prop`s). -/
theorem notInSupport_congr {D D' : CartierDivisor X.toScheme} (h : D = D')
    (hD : HasRegularCartierEquations X.toScheme D)
    (hD' : HasRegularCartierEquations X.toScheme D')
    (hC : C.NotInSupport D hD) : C.NotInSupport D' hD' := by
  subst h
  exact hC

/-- Transport of the intersection degree along an equality of divisors. -/
theorem intersectionDegree_congr {D D' : CartierDivisor X.toScheme} (h : D = D')
    (hD : HasRegularCartierEquations X.toScheme D)
    (hD' : HasRegularCartierEquations X.toScheme D')
    (hC : C.NotInSupport D hD) (hC' : C.NotInSupport D' hD') :
    C.intersectionDegree D hD hC = C.intersectionDegree D' hD' hC' := by
  subst h
  rfl

/-- **A prime curve off the support of `D` is off the support of every multiple `n • D`.** -/
theorem notInSupport_nsmul (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D) (hC : C.NotInSupport D hD) :
    ∀ (n : ℕ) (hn : HasRegularCartierEquations X.toScheme (n • D)),
      C.NotInSupport (n • D) hn := by
  intro n
  induction n with
  | zero =>
    intro hn
    exact C.notInSupport_congr (zero_nsmul D).symm
      (hasRegularCartierEquations_zero X.toScheme) hn
      (C.notInSupport_zero (hasRegularCartierEquations_zero X.toScheme))
  | succ n ih =>
    intro hn
    have hnD : HasRegularCartierEquations X.toScheme (n • D) :=
      CartierDivisorPullbackAdd.hasRegularCartierEquations_nsmul D hD n
    exact C.notInSupport_congr (succ_nsmul D n).symm
      (hasRegularCartierEquations_add hnD hD) hn
      (C.notInSupport_add (n • D) D hnD hD (ih hnD) hC)

/-- **Natural multiples of the restriction**: `(n • D)|_C = n • (D|_C)`.

The induction of the accepted `pullbackDivisor_nsmul`, transferred: the zero case is the unit law
`restrictCartier_zero`, the successor case splits `(n + 1) • D = n • D + D` with the accepted
`restrictCartier_add`, and `restrictCartier_congr` carries each identity through the divisor
argument. -/
theorem restrictCartier_nsmul (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D) (hC : C.NotInSupport D hD) :
    ∀ (n : ℕ) (hn : HasRegularCartierEquations X.toScheme (n • D))
      (hCn : C.NotInSupport (n • D) hn),
      C.restrictCartier (n • D) hn hCn = n • C.restrictCartier D hD hC := by
  intro n
  induction n with
  | zero =>
    intro hn hCn
    rw [C.restrictCartier_congr (zero_nsmul D) hn (hasRegularCartierEquations_zero X.toScheme)
        hCn (C.notInSupport_zero (hasRegularCartierEquations_zero X.toScheme)),
      C.restrictCartier_zero (hasRegularCartierEquations_zero X.toScheme)
        (C.notInSupport_zero (hasRegularCartierEquations_zero X.toScheme)),
      zero_nsmul]
  | succ n ih =>
    intro hn hCn
    have hnD : HasRegularCartierEquations X.toScheme (n • D) :=
      CartierDivisorPullbackAdd.hasRegularCartierEquations_nsmul D hD n
    have hCnD : C.NotInSupport (n • D) hnD := C.notInSupport_nsmul D hD hC n hnD
    rw [C.restrictCartier_congr (succ_nsmul D n) hn (hasRegularCartierEquations_add hnD hD)
        hCn (C.notInSupport_add (n • D) D hnD hD hCnD hC),
      C.restrictCartier_add (n • D) D hnD hD hCnD hC (hasRegularCartierEquations_add hnD hD)
        (C.notInSupport_add (n • D) D hnD hD hCnD hC),
      ih hnD hCnD, succ_nsmul]

/-- **`C · (n • D) = n * (C · D)`** for the scheme-theoretic intersection degree, by the same
induction over the accepted `intersectionDegree_add` and the unit law `intersectionDegree_zero`. -/
theorem intersectionDegree_nsmul (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D) (hC : C.NotInSupport D hD) :
    ∀ (n : ℕ) (hn : HasRegularCartierEquations X.toScheme (n • D))
      (hCn : C.NotInSupport (n • D) hn),
      C.intersectionDegree (n • D) hn hCn = n * C.intersectionDegree D hD hC := by
  intro n
  induction n with
  | zero =>
    intro hn hCn
    rw [C.intersectionDegree_congr (zero_nsmul D) hn (hasRegularCartierEquations_zero X.toScheme)
        hCn (C.notInSupport_zero (hasRegularCartierEquations_zero X.toScheme)),
      C.intersectionDegree_zero (hasRegularCartierEquations_zero X.toScheme)
        (C.notInSupport_zero (hasRegularCartierEquations_zero X.toScheme)),
      zero_mul]
  | succ n ih =>
    intro hn hCn
    have hnD : HasRegularCartierEquations X.toScheme (n • D) :=
      CartierDivisorPullbackAdd.hasRegularCartierEquations_nsmul D hD n
    have hCnD : C.NotInSupport (n • D) hnD := C.notInSupport_nsmul D hD hC n hnD
    rw [C.intersectionDegree_congr (succ_nsmul D n) hn (hasRegularCartierEquations_add hnD hD)
        hCn (C.notInSupport_add (n • D) D hnD hD hCnD hC),
      C.intersectionDegree_add (n • D) D hnD hD hCnD hC (hasRegularCartierEquations_add hnD hD)
        (C.notInSupport_add (n • D) D hnD hD hCnD hC),
      ih hnD hCnD, add_mul, one_mul]

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
