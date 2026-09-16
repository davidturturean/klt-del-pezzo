import KltDP.Geometry.PrimeCurveIntersectionAdditive
import KltDP.Geometry.EffectiveCartierZero

/-!
# The unit law for the restriction of a Cartier divisor to a prime curve

The restriction `D|_C` of a Cartier divisor with regular equations to a prime curve not contained in
its support is **additive** — the accepted `restrictCartier_add` and `intersectionDegree_add`
(`PrimeCurveIntersectionAdditive`) — but the accepted tree has no **unit** law for it. The sibling
functor does: the pullback carries `pullbackDivisor_zero` alongside `pullbackDivisor_add`. That
asymmetry is what this module removes.

* `notInSupport_zero` — a prime curve is never contained in the support of the zero divisor. The
  accepted `zeroCartierChart` (`EffectiveCartierZero`) has open `⊤`, equation `1` and coefficient
  `1`, so the germ at the generic point is `1`: **no germ computation is needed**, and in particular
  no chart of the surface has to be produced. Stated for an arbitrary proof
  `h0 : HasRegularCartierEquations X.toScheme 0`, so a consumer may pass either of the two accepted
  witnesses.
* `restrictCartier_congr` — the restriction does not depend on the presentation of the divisor; the
  companion of the accepted `pullbackDivisor_congr`, and what lets an identity like `0 + 0 = 0` be
  transported through the divisor argument without disturbing the two proof arguments (they are
  `Prop`s, so proof irrelevance closes it after `subst`).
* **`restrictCartier_zero`** — `0|_C = 0`, derived from additivity at `D₁ = D₂ = 0` exactly as the
  accepted `pullbackDivisor_zero` is derived from `pullbackDivisor_add`: `R = R + R` forces `R = 0`.
* **`intersectionDegree_zero`** — `C · 0 = 0` for the scheme-theoretic intersection degree, through
  the accepted `lineDegree_restrictCartier_eq_intersectionDegree` and `lineDegree_cartier_zero`.

Note `intersectionNumber_zero` is already accepted for the *Picard-theoretic* `intersectionNumber`,
which is defined for every Cartier divisor with no support hypothesis; the statements here are about
`restrictCartier`/`intersectionDegree`, which carry `NotInSupport` and are not the same declarations.

Nothing is admitted, no literature literal is used, and the whole import closure is accepted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)

/-- **A prime curve is never contained in the support of the zero divisor.** The accepted global
chart of `0` has coefficient `1`, whose germ is a unit at every point, so the support criterion
`mem_support_iff_not_isUnit_germ` closes immediately. -/
theorem notInSupport_zero (h0 : HasRegularCartierEquations X.toScheme 0) :
    C.NotInSupport 0 h0 := by
  intro hmem
  rw [mem_support_iff_not_isUnit_germ (0 : CartierDivisor X.toScheme) h0
    (zeroCartierChart X.toScheme) C.genericPoint (Set.mem_univ _)] at hmem
  apply hmem
  show IsUnit (X.toScheme.presheaf.germ ⊤ C.genericPoint (Set.mem_univ _)
    (1 : Γ(X.toScheme, ⊤)))
  rw [map_one]
  exact isUnit_one

/-- The restriction does not depend on the presentation of the divisor (the companion of the
accepted `pullbackDivisor_congr`; the two proof arguments are `Prop`s). -/
theorem restrictCartier_congr {D D' : CartierDivisor X.toScheme} (h : D = D')
    (hD : HasRegularCartierEquations X.toScheme D)
    (hD' : HasRegularCartierEquations X.toScheme D')
    (hC : C.NotInSupport D hD) (hC' : C.NotInSupport D' hD') :
    C.restrictCartier D hD hC = C.restrictCartier D' hD' hC' := by
  subst h
  rfl

/-- **The unit law for the restriction**: `0|_C = 0`.

Additivity at `D₁ = D₂ = 0` gives `0|_C = 0|_C + 0|_C` once `0 + 0 = 0` is transported through the
divisor argument, and an element equal to its own double is zero. This is the derivation the accepted
`pullbackDivisor_zero` makes for the sibling functor. -/
theorem restrictCartier_zero (h0 : HasRegularCartierEquations X.toScheme 0)
    (hC0 : C.NotInSupport 0 h0) :
    C.restrictCartier 0 h0 hC0 = 0 := by
  have hsum := C.restrictCartier_add 0 0 h0 h0 hC0 hC0
    (hasRegularCartierEquations_add h0 h0) (C.notInSupport_add 0 0 h0 h0 hC0 hC0)
  rw [C.restrictCartier_congr (add_zero (0 : CartierDivisor X.toScheme))
    (hasRegularCartierEquations_add h0 h0) h0 (C.notInSupport_add 0 0 h0 h0 hC0 hC0) hC0] at hsum
  exact left_eq_add.mp hsum

/-- **`C · 0 = 0`** for the scheme-theoretic intersection degree: the zero scheme of `0|_C = 0` is
empty. Proved through the accepted degree bridge rather than by computing the empty scheme. -/
theorem intersectionDegree_zero (h0 : HasRegularCartierEquations X.toScheme 0)
    (hC0 : C.NotInSupport 0 h0) :
    C.intersectionDegree 0 h0 hC0 = 0 := by
  have h := C.lineDegree_restrictCartier_eq_intersectionDegree 0 h0 hC0
  rw [C.restrictCartier_zero h0 hC0, C.lineDegree_cartier_zero] at h
  exact_mod_cast h.symm

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
