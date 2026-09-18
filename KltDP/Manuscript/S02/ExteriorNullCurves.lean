import KltDP.Manuscript.S02.Projection
import KltDP.Geometry.NumericalHodgeConsequences
import KltDP.Geometry.ArithmeticCurveAdjunction
import KltDP.Geometry.GenusZeroCurveProjectiveLineIso
import KltDP.Geometry.SurfaceNumericalFinitenessProved
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Manuscript Lemma 2.9: null curves outside the minimal exceptional divisor

Source: `source/manuscript.tex`, lines 638–664, label `lem:exterior-null-curves`.

For the resolution datum `(S, D, L)` of a rank-one klt del Pezzo surface and a numerical
class `G ∈ N¹(S)_ℚ` which is nef (`G · C ≥ 0` on every prime curve) and big (`G² > 0`),
every exterior prime curve `Q ⊄ D` with `G · Q = 0` satisfies

* `exteriorNullCurve_isMinusOne`: `Q` is a `(-1)`-curve (`Q ≅ P¹`, `Q² = -1`) and
  `K_S · Q = -1`;
* `exteriorNullCurves_disjoint`: two distinct such curves are disjoint;
* `exteriorNullCurves_finite`: there are only finitely many such curves.

Proof (manuscript lines 653–663). Hodge (`NumericalHodgeConsequences.neg_of_orthogonal_to_positive`)
gives `Q² < 0`. Since `Q ⊄ D`, `K_S · Q = -L·Q - Σ λ_i (D_i · Q) < 0` because `L · Q > 0`
(`Ldeg_pos`), `λ_i ≥ 0` and `D_i · Q ≥ 0`. Arithmetic adjunction
(`arithmetic_canonical_degree`: `K_S · Q = 2 p_a(Q) - 2 - Q²` for an arbitrary prime curve) then
forces `Q² = K_S · Q = -1` and `p_a(Q) = 0`, and a proper integral curve of arithmetic genus zero
is `P¹` (`GenusZeroCurveProjectiveLineIso.exists_iso`). If two such curves met with
`Q₁ · Q₂ = m ≥ 1`, the class `[Q₁] + [Q₂]` would be orthogonal to `G` with square `2m - 2 ≥ 0`,
hence zero by Hodge, contradicting `L · ([Q₁] + [Q₂]) > 0`. Finally the classes of the null
curves are pairwise orthogonal of square `-1`, hence linearly independent in the
finite-dimensional space `N¹(S)_ℚ`, so there are finitely many of them (this replaces the
manuscript's lattice count, which is not needed).

The nefness hypothesis `hnef` is kept for fidelity to the manuscript statement; the proofs only
use `G² > 0` and `G · Q = 0`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript

universe u

namespace KltDP.Manuscript.S02

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-! ### Degrees on exterior curves -/

/-- The contacts `Q · D_i` of an exterior prime curve are nonnegative. -/
theorem contact_nonneg_of_not_exceptional (Q : R.S.PrimeCurve) (hQ : ¬ IsExceptionalCurve R.π Q)
    (i : R.Vertices) : 0 ≤ R.contact Q i := by
  have hne : Q ≠ i.val := by
    intro h
    apply hQ
    rw [h]
    exact i.property
  have h := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg Q i.val hne
  rwa [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber] at h

/-- `K_S · Q < 0` for every exterior prime curve `Q` (manuscript lines 655–658):
`K_S · Q = -L · Q - Σ λ_i (D_i · Q)` with `L · Q > 0`, `λ_i ≥ 0`, `D_i · Q ≥ 0`. -/
theorem Kdeg_neg_of_not_exceptional (Q : R.S.PrimeCurve) (hQ : ¬ IsExceptionalCurve R.π Q) :
    R.Kdeg Q < 0 := by
  have h := R.Ldeg_eq_neg_Kdeg_sub Q
  have hpos := Ldeg_pos R Q hQ
  have hsum : 0 ≤ ∑ i : R.Vertices, R.lam i *
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℚ) := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (R.lam_nonneg i)
    exact_mod_cast contact_nonneg_of_not_exceptional R Q hQ i
  have hK : (R.Kdeg Q : ℚ) < 0 := by linarith
  exact_mod_cast hK

/-! ### Manuscript Lemma 2.9 -/

/-- Manuscript Lemma 2.9 (`lem:exterior-null-curves`, lines 638–664), first part: an exterior
prime curve `Q ⊄ D` which is null for a nef and big class `G` is a `(-1)`-curve
(`Q ≅ P¹`, `Q² = -1`) with `K_S · Q = -1`. -/
theorem exteriorNullCurve_isMinusOne (G : R.S.NumericalClassGroup)
    (hnef : ∀ C : R.S.PrimeCurve, 0 ≤ R.S.numericalRestrictionDegree C G)
    (hbig : 0 < R.S.numericalIntersectionBilinForm R.hreg G G)
    (Q : R.S.PrimeCurve) (hQ : ¬ IsExceptionalCurve R.π Q)
    (hnull : R.S.numericalRestrictionDegree Q G = 0) :
    IsMinusOneCurve R.hreg Q ∧ R.Kdeg Q = -1 := by
  -- Hodge: `Q² < 0`
  have hperp : R.S.numericalIntersectionBilinForm R.hreg G
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg Q) = 0 := by
    rw [DisjointNegativeCurvesRank.pairing_curveClass R.S R.hreg]
    exact hnull
  have hneg := NumericalHodgeConsequences.neg_of_orthogonal_to_positive R.S R.hreg G
    (DisjointNegativeCurvesRank.curveClass R.S R.hreg Q) hbig hperp
    (NefNullCurveNegativeSquare.curveClass_ne_zero R.S R.hreg Q)
  rw [curveClass_self_pairing R Q] at hneg
  have hsq : Q.selfIntersectionNumber R.hreg < 0 := by exact_mod_cast hneg
  -- `K_S · Q < 0`
  have hK := Kdeg_neg_of_not_exceptional R Q hQ
  -- arithmetic adjunction `K_S · Q = 2 p_a(Q) - 2 - Q²`
  have hadj := R.S.arithmetic_canonical_degree R.hreg R.KS R.eKS Q
  change R.Kdeg Q = 2 * (CurveCanonical.genus Q.toSpec : ℤ) - 2 -
    Q.selfIntersectionNumber R.hreg at hadj
  have hgenus : CurveCanonical.genus Q.toSpec = 0 := by omega
  have hself : Q.selfIntersectionNumber R.hreg = -1 := by omega
  have hKQ : R.Kdeg Q = -1 := by omega
  refine ⟨⟨?_, hself⟩, hKQ⟩
  letI : IsProper Q.toSpec := Q.toSpec_isProper
  exact GenusZeroCurveProjectiveLineIso.exists_iso Q.toSpec Q.dimension_one_toScheme hgenus

/-- Two distinct exterior null curves have intersection number zero (manuscript lines
659–663: otherwise `[Q₁] + [Q₂]` would be a nonzero class orthogonal to `G` with nonnegative
square). -/
theorem exteriorNullCurves_intersectionPairing_eq_zero (G : R.S.NumericalClassGroup)
    (hnef : ∀ C : R.S.PrimeCurve, 0 ≤ R.S.numericalRestrictionDegree C G)
    (hbig : 0 < R.S.numericalIntersectionBilinForm R.hreg G G)
    (Q₁ Q₂ : R.S.PrimeCurve) (h₁ : ¬ IsExceptionalCurve R.π Q₁) (h₂ : ¬ IsExceptionalCurve R.π Q₂)
    (hn₁ : R.S.numericalRestrictionDegree Q₁ G = 0) (hn₂ : R.S.numericalRestrictionDegree Q₂ G = 0)
    (hne : Q₁ ≠ Q₂) :
    R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg Q₁)
      (R.S.primeCurveCartier R.hreg Q₂) = 0 := by
  have hs₁ := (exteriorNullCurve_isMinusOne R G hnef hbig Q₁ h₁ hn₁).1.selfIntersection
  have hs₂ := (exteriorNullCurve_isMinusOne R G hnef hbig Q₂ h₂ hn₂).1.selfIntersection
  have hm := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg Q₁ Q₂ hne
  by_contra hm0
  have hm1 : 1 ≤ R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg Q₁)
      (R.S.primeCurveCartier R.hreg Q₂) := by omega
  -- the class `c = [Q₁] + [Q₂]`
  obtain ⟨c, hc⟩ : ∃ c : R.S.NumericalClassGroup,
      c = DisjointNegativeCurvesRank.curveClass R.S R.hreg Q₁ +
        DisjointNegativeCurvesRank.curveClass R.S R.hreg Q₂ := ⟨_, rfl⟩
  -- `G · c = 0`
  have hperp : R.S.numericalIntersectionBilinForm R.hreg G c = 0 := by
    rw [hc, LinearMap.BilinForm.add_right, DisjointNegativeCurvesRank.pairing_curveClass R.S R.hreg,
      DisjointNegativeCurvesRank.pairing_curveClass R.S R.hreg, hn₁, hn₂, add_zero]
  -- `c² = -1 + 2 m - 1 ≥ 0`
  have hself₁ : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg Q₁)
      (R.S.primeCurveCartier R.hreg Q₁) = -1 := by
    rw [R.S.intersectionPairing_primeCurve R.hreg]
    exact hs₁
  have hself₂ : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg Q₂)
      (R.S.primeCurveCartier R.hreg Q₂) = -1 := by
    rw [R.S.intersectionPairing_primeCurve R.hreg]
    exact hs₂
  have hsymm := R.S.intersectionPairing_symm R.hreg (R.S.primeCurveCartier R.hreg Q₂)
    (R.S.primeCurveCartier R.hreg Q₁)
  have hcc : 0 ≤ R.S.numericalIntersectionBilinForm R.hreg c c := by
    rw [hc, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right]
    simp only [DisjointNegativeCurvesRank.curveClass_pairing]
    rw [hself₁, hself₂, hsymm]
    have h1 : (1 : ℚ) ≤ (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg Q₁)
      (R.S.primeCurveCartier R.hreg Q₂) : ℚ) := by exact_mod_cast hm1
    push_cast
    linarith
  -- Hodge forces `c = 0`, but `L · c = L · Q₁ + L · Q₂ > 0`
  have hc0 := NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal R.S R.hreg G c
    hbig hperp hcc
  have hL : R.S.numericalIntersectionBilinForm R.hreg R.Lnum c = R.Ldeg Q₁ + R.Ldeg Q₂ := by
    rw [hc, LinearMap.BilinForm.add_right, Lnum_pairing_curveClass R, Lnum_pairing_curveClass R]
  rw [hc0, map_zero] at hL
  have hp₁ := Ldeg_pos R Q₁ h₁
  have hp₂ := Ldeg_pos R Q₂ h₂
  linarith

/-- Manuscript Lemma 2.9, second part: two distinct exterior null curves are disjoint. -/
theorem exteriorNullCurves_disjoint (G : R.S.NumericalClassGroup)
    (hnef : ∀ C : R.S.PrimeCurve, 0 ≤ R.S.numericalRestrictionDegree C G)
    (hbig : 0 < R.S.numericalIntersectionBilinForm R.hreg G G)
    (Q₁ Q₂ : R.S.PrimeCurve) (h₁ : ¬ IsExceptionalCurve R.π Q₁) (h₂ : ¬ IsExceptionalCurve R.π Q₂)
    (hn₁ : R.S.numericalRestrictionDegree Q₁ G = 0) (hn₂ : R.S.numericalRestrictionDegree Q₂ G = 0)
    (hne : Q₁ ≠ Q₂) : Disjoint (Q₁ : Set R.S.toScheme) (Q₂ : Set R.S.toScheme) :=
  (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint R.S R.hreg
    Q₁ Q₂ hne).mp
    (exteriorNullCurves_intersectionPairing_eq_zero R G hnef hbig Q₁ Q₂ h₁ h₂ hn₁ hn₂ hne)

/-- Manuscript Lemma 2.9, third part: there are only finitely many exterior null curves.
Their classes are pairwise orthogonal of square `-1`, hence linearly independent in the
finite-dimensional space `N¹(S)_ℚ`. -/
theorem exteriorNullCurves_finite (G : R.S.NumericalClassGroup)
    (hnef : ∀ C : R.S.PrimeCurve, 0 ≤ R.S.numericalRestrictionDegree C G)
    (hbig : 0 < R.S.numericalIntersectionBilinForm R.hreg G G) :
    {Q : R.S.PrimeCurve | ¬ IsExceptionalCurve R.π Q ∧
      R.S.numericalRestrictionDegree Q G = 0}.Finite := by
  classical
  haveI : FiniteDimensional ℚ R.S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalSpaceFiniteDimensional R.S R.hreg
  have hli : LinearIndependent ℚ
      (fun Q : {Q : R.S.PrimeCurve | ¬ IsExceptionalCurve R.π Q ∧
          R.S.numericalRestrictionDegree Q G = 0} =>
        DisjointNegativeCurvesRank.curveClass R.S R.hreg Q.val) := by
    refine LinearMap.BilinForm.linearIndependent_of_iIsOrtho
      (B := R.S.numericalIntersectionBilinForm R.hreg) ?_ ?_
    · intro Q₁ Q₂ hne
      obtain ⟨h₁, hn₁⟩ := Q₁.property
      obtain ⟨h₂, hn₂⟩ := Q₂.property
      have hne' : Q₁.val ≠ Q₂.val := fun h => hne (Subtype.ext h)
      show R.S.numericalIntersectionBilinForm R.hreg
        (DisjointNegativeCurvesRank.curveClass R.S R.hreg Q₁.val)
        (DisjointNegativeCurvesRank.curveClass R.S R.hreg Q₂.val) = 0
      rw [DisjointNegativeCurvesRank.curveClass_pairing R.S R.hreg]
      exact_mod_cast exteriorNullCurves_intersectionPairing_eq_zero R G hnef hbig Q₁.val Q₂.val
        h₁ h₂ hn₁ hn₂ hne'
    · intro Q
      obtain ⟨hQ, hnull⟩ := Q.property
      show ¬ R.S.numericalIntersectionBilinForm R.hreg
        (DisjointNegativeCurvesRank.curveClass R.S R.hreg Q.val)
        (DisjointNegativeCurvesRank.curveClass R.S R.hreg Q.val) = 0
      rw [curveClass_self_pairing R Q.val,
        (exteriorNullCurve_isMinusOne R G hnef hbig Q.val hQ hnull).1.selfIntersection]
      norm_num
  haveI := hli.finite_of_isNoetherian
  exact Set.toFinite _

end KltDP.Manuscript.S02

#print axioms KltDP.Manuscript.S02.exteriorNullCurve_isMinusOne
#print axioms KltDP.Manuscript.S02.exteriorNullCurves_disjoint
#print axioms KltDP.Manuscript.S02.exteriorNullCurves_finite
