import KltDP.Manuscript.S07.FiberDegreeEquality
import KltDP.Geometry.PrimeCurvePairingOnePoint

/-!
# Manuscript Lemma 7.2: ramification of a smooth bisection

Source: `source/manuscript.tex`, lines 2066–2136, `lem:bisection-ramification`.

Let `g : S → P¹` be the ruling with fibre class `F`, and let `B ⊂ S` be a smooth rational curve
with `F · B = 2` (a *bisection*), so that `h = g|_B : B → P¹` is a finite morphism of degree two
(`bisection_pullback_degree`: `h^*O(1) = i^*O(F)` has degree `F · B = 2` on `B`).

**What Theorem 7.5 uses** (and what this file provides):

* (i) the multiplicity formula in the form needed: if `B` meets the fibre over `t` only in the
  unique exterior component `R₀` (i.e. `B · C = 0` for every other component), transversally
  (`B · R₀ = 1`), then the set-theoretic fibre `h⁻¹(t) = B ∩ g⁻¹(t)` is a single point `x`
  (`bisectionFiber_singleton`); since `h^*t` has degree `2` on `B`, this means `h^*t = 2x`, i.e.
  `x` is a ramification point of `h`.
* (ii) Riemann–Hurwitz for the separable tame degree-two map `h : P¹ → P¹` (`p ≠ 2`): there are at
  most two ramification points, i.e. at most two closed `t` with `#h⁻¹(t) = 1`.

The union contains no Riemann–Hurwitz theorem (its Hurwitz material concerns quadratic covers of
surfaces), so (ii) is **not** proved here and **no axiom is admitted**: it is isolated as the
explicit hypothesis `RiemannHurwitzDegreeTwo`, threaded through `bisectionRamification_count`.
Its exact content is stated in the docstring of `RiemannHurwitzDegreeTwo`:

> *Riemann–Hurwitz* (Hartshorne IV.2.4 with IV.2.2(b); Stacks 0C1B, "different form"), instance
> `X = B ≅ P¹_k → Y = P¹_k`, `deg h = 2`, `k` algebraically closed of characteristic `p ≠ 2`: `h` is
> separable (its inseparable degree is a power of `p` dividing `2`) and tame (all `e_x ≤ 2 < p`, or
> `p = 0`… here `p > 2`), so `2g(B) − 2 = 2 (2g(P¹) − 2) + Σ_x (e_x − 1)`, i.e. `Σ_x (e_x − 1) = 2`;
> a closed point `t` with `#h⁻¹(t) = 1` has `e_x = deg h = 2` at its unique preimage `x`, hence
> there are at most two such `t`.

The remaining manuscript clauses (the `p = 2` separable and inseparable cases) are not needed for
Theorem 1.1 (`p > 2`) and are not formalised.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S03

universe u

namespace KltDP.Manuscript.S07

variable {k : Type u} [Field k] [IsAlgClosed k] {R : ResolutionDatum k}
  (p : ℕ) [CharP k p]
  (F : CartierDivisor R.S.toScheme)
  (g : R.S.toScheme ⟶ projectiveSpace k 1)
  (hg : g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism)
  (e : (pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
    cartierDivisorModule R.S.toScheme F)

/-! ### The degree of `h = g|_B` -/

include e in
/-- `h = g|_B` has degree `F · B`: the line bundle `h^*O(1) = i_B^*O(F)` has degree `F · B` on `B`
(so a bisection gives a degree-two map `B → P¹`). -/
theorem bisection_pullback_degree (B : R.S.PrimeCurve) :
    B.lineDegree (pullbackInvertibleSheaf (B.inclusion ≫ g)
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)) = B.intersectionNumber F := by
  rw [← B.restrictionDegree_pullback g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1),
    B.restrictionDegree_eq_of_iso
      (L := pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1))
      (M := cartierDivisorInvertibleSheaf R.S.toScheme F) e]
  rfl

/-! ### (i) The fibre of `h` over `t` when `B` meets only the exterior component -/

/-- If `B` is disjoint from every component of the fibre over `t` other than `R₀`, then
`B ∩ g⁻¹(t) = B ∩ R₀`. -/
theorem bisectionFiber_eq_inter {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (B R₀ : R.S.PrimeCurve) (hR₀ : InFiber g t R₀)
    (hdisj : ∀ C, InFiber g t C → C ≠ R₀ → Disjoint (B : Set R.S.toScheme) (C : Set R.S.toScheme)) :
    (B : Set R.S.toScheme) ∩ g.base ⁻¹' {t} = (B : Set R.S.toScheme) ∩ (R₀ : Set R.S.toScheme) := by
  ext x
  constructor
  · rintro ⟨hxB, hxt⟩
    have hx : x ∈ ⋃ C : {C : R.S.PrimeCurve // InFiber g t C}, (C.1 : Set R.S.toScheme) := by
      rw [iUnion_inFiber_eq R F g hE]
      exact hxt
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    by_cases hC : C.1 = R₀
    · exact ⟨hxB, hC ▸ hxC⟩
    · exact ((Set.disjoint_left.mp (hdisj C.1 C.2 hC)) hxB hxC).elim
  · rintro ⟨hxB, hxR⟩
    exact ⟨hxB, hR₀ x hxR⟩

/-- **Manuscript Lemma 7.2 (i), the form used in Theorem 7.5** (lines 2094–2099, 2128–2135): if `B`
meets the fibre over `t` only in the component `R₀`, transversally (`B · R₀ = 1`), then the
set-theoretic fibre of `h = g|_B` over `t` is a single point `x` (so `h^*t = 2x`: the divisor `h^*t`
has degree `F · B = 2` and is supported at `x`). -/
theorem bisectionFiber_singleton {t : projectiveSpace k 1} {E : CartierDivisor R.S.toScheme}
    (hE : IsFiberDivisor F g t E) (B R₀ : R.S.PrimeCurve) (hR₀ : InFiber g t R₀) (hne : B ≠ R₀)
    (hBR : B.intersectionNumber (R.S.primeCurveCartier R.hreg R₀) = 1)
    (hdisj : ∀ C, InFiber g t C → C ≠ R₀ → Disjoint (B : Set R.S.toScheme) (C : Set R.S.toScheme)) :
    ∃ x : R.S.toScheme, (B : Set R.S.toScheme) ∩ g.base ⁻¹' {t} = {x} := by
  rw [bisectionFiber_eq_inter F g hE B R₀ hR₀ hdisj]
  have hpair : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg B)
      (R.S.primeCurveCartier R.hreg R₀) = 1 := by
    rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]
    exact hBR
  have hsub : ((B : Set R.S.toScheme) ∩ (R₀ : Set R.S.toScheme)).Subsingleton :=
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_le_one_inter_subsingleton R.S R.hreg
      B R₀ hne (le_of_eq hpair)
  have hnonempty : ((B : Set R.S.toScheme) ∩ (R₀ : Set R.S.toScheme)).Nonempty := by
    rw [← Set.not_disjoint_iff_nonempty_inter,
      ← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint R.S R.hreg
        B R₀ hne, hpair]
    exact one_ne_zero
  obtain ⟨x, hx⟩ := hnonempty
  exact ⟨x, hsub.eq_singleton_of_mem hx⟩

include hg e in
/-- A bisection is not contained in any fibre (`F · B = 2 ≠ 0`), hence differs from every fibre
component. -/
theorem bisection_ne_of_inFiber (B : R.S.PrimeCurve) (hFB : B.intersectionNumber F = 2)
    {t : projectiveSpace k 1} (C : R.S.PrimeCurve) (hC : InFiber g t C) : B ≠ C := by
  intro h
  have h0 := intersectionNumber_eq_zero_of_vertical R F g hg e C t hC
  rw [← h, hFB] at h0
  exact absurd h0 (by norm_num)

/-! ### (ii) Riemann–Hurwitz, as an explicit hypothesis -/

/-- **Riemann–Hurwitz instance (explicit hypothesis, not proved in the union).**

Statement (Hartshorne, *Algebraic Geometry*, IV.2.4 together with IV.2.2(b); Stacks Project
Tag 0C1B, "Riemann–Hurwitz, different form"): for a finite separable morphism `h : X → Y` of
smooth projective curves over an algebraically closed field, `2g(X) − 2 = deg(h) (2g(Y) − 2) +
deg R` where `R = Σ_x (e_x − 1) x` is the ramification divisor when `h` is tamely ramified
(`p ∤ e_x` for all `x`), and `Σ_{x ∈ h⁻¹(t)} e_x = deg h` for every closed point `t`.

Instance used here: `X = B`, a smooth rational curve on `S` (`B ≅ P¹_k`), `Y = P¹_k`,
`h = g|_B` of degree `F · B = 2` (`bisection_pullback_degree`), `k` algebraically closed of
characteristic `p ≠ 2`. Then `h` is separable (its inseparable degree is a power of `p` dividing
`2`) and tame (every `e_x ∈ {1, 2}` is prime to `p`), and Riemann–Hurwitz gives
`Σ_x (e_x − 1) = −2 − 2·(−2) = 2`. A closed point `t` whose set-theoretic fibre `h⁻¹(t) = B ∩ g⁻¹(t)`
is a single point `x` has `e_x = 2`. Hence there are **at most two** such closed points `t`.

The predicate records exactly this conclusion, under exactly these premises. -/
def RiemannHurwitzDegreeTwo (B : R.S.PrimeCurve) : Prop :=
  (∃ e : B.toScheme ≅ projectiveSpace k 1, e.hom ≫ projectiveSpaceToSpec k 1 = B.toSpec) →
  B.intersectionNumber F = 2 → p ≠ 2 →
  ∀ T : Finset (projectiveSpace k 1),
    (∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)) ∧
      ∃ x : R.S.toScheme, (B : Set R.S.toScheme) ∩ g.base ⁻¹' {t} = {x}) →
    T.card ≤ 2

set_option linter.unusedSectionVars false in
include hg e in
/-- **Manuscript Lemma 7.2, the count used in Theorem 7.5** (lines 2066–2099, 2128–2135, and
`eq:one-bisection-ramification-budget`): let `B ⊂ D` be an exceptional bisection (`B ≅ P¹`,
`F · B = 2`), `p ≠ 2`, and let `T` be a finite set of closed points `t` such that `B` meets the
fibre over `t` only in one component `R₀ = R₀(t)`, with `B · R₀ = 1` and `B · C = 0` for every
other component `C` (in Theorem 7.5, `R₀` is the unique exterior component, of multiplicity two).
Each such `t` is a branch point of the tame degree-two map `h = g|_B` (`h^*t = 2x`), so by
Riemann–Hurwitz (`hRH`) there are at most two of them. -/
theorem bisectionRamification_count (B : R.S.PrimeCurve) (hB : IsExceptionalCurve R.π B)
    (hFB : B.intersectionNumber F = 2) (hp2 : p ≠ 2) (hRH : RiemannHurwitzDegreeTwo p F g B)
    (T : Finset (projectiveSpace k 1))
    (hT : ∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)) ∧
      ∃ (E : CartierDivisor R.S.toScheme) (R₀ : R.S.PrimeCurve), IsFiberDivisor F g t E ∧
        InFiber g t R₀ ∧ B.intersectionNumber (R.S.primeCurveCartier R.hreg R₀) = 1 ∧
        ∀ C, InFiber g t C → C ≠ R₀ → B.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0) :
    T.card ≤ 2 := by
  refine hRH (R.exceptional_rational B hB) hFB hp2 T fun t ht => ?_
  obtain ⟨hcl, E, R₀, hE, hR₀, hBR, hzero⟩ := hT t ht
  refine ⟨hcl, bisectionFiber_singleton F g hE B R₀ hR₀ (bisection_ne_of_inFiber F g hg e B hFB R₀ hR₀)
    hBR fun C hC hCR₀ => ?_⟩
  have hne : B ≠ C := bisection_ne_of_inFiber F g hg e B hFB C hC
  rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint R.S R.hreg
    B C hne, PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]
  exact hzero C hC hCR₀

end KltDP.Manuscript.S07

#print axioms KltDP.Manuscript.S07.bisection_pullback_degree
#print axioms KltDP.Manuscript.S07.bisectionFiber_singleton
#print axioms KltDP.Manuscript.S07.bisectionRamification_count
