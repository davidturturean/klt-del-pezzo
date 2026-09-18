import KltDP.Geometry.CurveConeReal
import KltDP.Geometry.NumericalOneCycles
import KltDP.Geometry.NefNullCurveNegativeSquare
import KltDP.Geometry.SmoothCanonicalExteriorComparison
import KltDP.Geometry.Surface

/-!
# Tanaka's contraction theorem for extremal rays (Theorem 4.4), as an exact instance

**Source.** Hiromu Tanaka, *Minimal model program for excellent surfaces*, Annales de
l'Institut Fourier 68 (2018), no. 1, 345–376, doi:10.5802/aif.3163, Theorem 4.4 (printed
p. 365; extracted text `tanaka2018.txt` lines 1012–1029). Verbatim statement:

> **Theorem 4.4.** — Let B be a scheme satisfying Assumption 2.1. Let π : X → S be a projective
> B-morphism from a quasi-projective normal B-surface X to a quasi-projective B-scheme S. Let Δ
> be an R-divisor on X such that 0 ≤ Δ ≤ 1 and K_{X/B} + Δ is R-Cartier. Let R be an extremal
> ray of NE(X/S) which is (K_{X/B} + Δ)-negative. Then there exists a projective S-morphism
> f : X → Y to a projective S-scheme Y that satisfies the following properties.
> (1) f_*O_X = O_Y.
> (2) For any projective S-curve C on X such that π(C) is one point, f(C) is one point if and
>     only if [C] ∈ R.
> (3) If dim Y ≥ 1, then the sequence 0 → Pic Y → Pic X → Z is exact for any projective
>     S-curve C on X such that f(C) is one point.
> (4) ρ(Y/S) = ρ(X/S) − 1.
> (5) If X is Q-factorial, then Y is Q-factorial and the fibre f^{-1}(y) of any closed point
>     y ∈ Y is irreducible.

**Instance admitted here** (`contraction_44_instance`), with every specialization recorded:

* `B = S = Spec k` for an algebraically closed field `k`. A field is excellent, regular,
  separated and of finite dimension, so `Spec k` satisfies Tanaka's Assumption 2.1 (text lines
  ~250–262).
* `X = S.toScheme` for an actual regular normal projective surface `S : NormalProjectiveSurface k`
  (integral, separated, of finite type and dimension two over `k`, normal since regular), and
  `π = S.structureMorphism`, which is projective (the surface is projective over `k`), so `X`
  is a quasi-projective normal `B`-surface and `π` a projective `B`-morphism to the
  quasi-projective `B`-scheme `S = Spec k`.
* `Δ = 0`, which satisfies `0 ≤ Δ ≤ 1`; then `K_{X/B} + Δ = K_S`, represented by the Cartier
  divisor `KS` whose divisor sheaf is the canonical sheaf `ω_{S/k} = ∧² Ω_{S/k}` (`eKS`), hence
  `R`-Cartier.
* `NE(X/S) = NE(S/Spec k)` is the closed cone of curves `closedCurveCone S hreg` in the real
  Néron–Severi model `V S` of `KltDP.Geometry.CurveConeReal`: Tanaka's `N_1(X/S)_ℝ` is identified
  with `V S = N¹(S)_ℝ` through the perfect intersection pairing
  (`KltDP.Geometry.NumericalOneCycles.rhoReal_eq_picardRank` and `pairingMap`), which carries the
  class of a curve `C` to `curveClassReal S hreg C` (`pairReal_curveClassReal`). An extremal ray
  `R = ℝ_{≥0} v` is `IsExtremalRay S (closedCurveCone S hreg) v` (Kollár–Mori, Definition 1.16,
  the definition Tanaka uses), and `(K_{X/B} + Δ)`-negativity of `R` is
  `pairReal S hreg (cartierClass S KS) v < 0`.
* Conclusions: a morphism `f : S.toScheme ⟶ Y` over `k` to a scheme `Y` projective over `k`
  (`IsProjectiveOverField g`); a morphism between projective `k`-schemes is a projective
  `S`-morphism, and `Y` is a projective `S`-scheme. (1) `f_*O_X = O_Y` is `IsIso f.c`. (2) The
  projective `S`-curves `C` on `X` with `π(C)` a point are all prime curves of `S` (the image in
  `Spec k` is always a point); `f(C)` is one point iff `[C] ∈ R`, i.e.
  `curveClassReal S hreg C ∈ ray S v`. (4) `ρ(Y/S) = ρ(X/S) − 1`, with Tanaka's
  `ρ = dim_ℝ N_1(·/S)_ℝ` (text lines ~540–560; intersection numbers as in his Definition 2.6,
  `Positivity.subvarietyDegree`, the coefficient of `m` in `χ(C, L^m)`) formalized as
  `NumericalOneCycles.rhoReal`; on the source `ρ(X/S) = rhoReal S.toScheme S.structureMorphism
  = S.picardRank` by `rhoReal_eq_picardRank`, so (4) is stated as `rhoReal Y g + 1 = S.picardRank`.
* Conclusions (3) and (5) are omitted (an instance with fewer conclusions is implied by the
  theorem). Nothing is added: no manuscript consequence is packaged into the axiom.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.CurveCone
open KltDP.Geometry.NumericalOneCycles

universe u

namespace KltDP.Literature.Tanaka

/-- **Tanaka, Theorem 4.4 (AIF 68 (2018), p. 365), exact instance** with `B = S = Spec k`,
`X` an actual regular projective surface, `Δ = 0`, conclusions (1), (2), (4). See the module
docstring for the verbatim statement and every specialization. -/
axiom contraction_44_instance {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [FiniteDimensional ℚ S.NumericalClassGroup]
    (hreg : ∀ x : S.Point, RegularPoint S.toScheme x)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (v : V S) (hv : IsExtremalRay S (closedCurveCone S hreg) v)
    (hneg : pairReal S hreg (NefNullCurveNegativeSquare.cartierClass S KS) v < 0) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of k)) (f : S.toScheme ⟶ Y),
      IsProjectiveOverField g ∧
      f ≫ g = S.structureMorphism ∧
      IsIso f.c ∧
      (∀ C : S.PrimeCurve,
        (∃ y : Y, f.base '' (C : Set S.toScheme) = {y}) ↔
          curveClassReal S hreg C ∈ ray S v) ∧
      rhoReal Y g + 1 = S.picardRank

end KltDP.Literature.Tanaka

#print axioms KltDP.Literature.Tanaka.contraction_44_instance
