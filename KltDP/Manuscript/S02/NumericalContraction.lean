import KltDP.Manuscript.S02.AnticanonicalContraction
import KltDP.Manuscript.S02.Stieltjes
import KltDP.Geometry.AmpleCurveRestrictionPositive
import KltDP.Geometry.AmpleBignessFromRiemannRoch
import KltDP.Geometry.AmplePositivity
import KltDP.Geometry.PrimeCurvePairingSupport
import KltDP.LinearAlgebra.Stieltjes
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Manuscript Theorem 2.7: numerical rank-one contraction

Source: `source/manuscript.tex`, lines 560–603, label `thm:numerical-contraction`.

Same forest `G : ι → T.PrimeCurve` as in Theorem 2.6, `B = Σ β_i G_i` with `β_i < 1`,
`H = -(K_T + B)` cleared to the Cartier divisor `Hm = m H`, with `Hm · G_i = 0` for every `i`,
`Hm² > 0`, and `Hm · C₀ > 0` for one prime curve `C₀` not among the `G_i`.  Then the conclusion of
Theorem 2.6 holds: `G` has a projective contraction `f : T → Y` to a rank-one klt del Pezzo surface
with `K_T + B = f^*K_Y`.

Proof (manuscript): an ample `A₀`, `a_i = A₀ · G_i > 0`, `x = A_G⁻¹ a ≥ 0` (Lemma 2.1, Stieltjes),
`M = A₀ + Σ x_i G_i` is orthogonal to every `G_i` and has positive degree on every curve outside `G`;
`H` and `M` both lie in the one-dimensional orthogonal complement of the independent classes
`[G_i]` (`card ι + 1 = ρ(T)`), so `H ≡ c M` with `c > 0` (degree on `C₀`); hence `H` is nef with
null locus exactly `G`, and Theorem 2.6 applies.

The manuscript's additional hypotheses "intersection matrix negative definite" and "classes
independent" are not needed as inputs: both follow (Hodge index, the union's
`NullCurveIntersectionMatrix` / `NullCurveIndependenceRank`) from `Hm² > 0` and `Hm · G_i = 0`;
rationality of `T` is not used.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

universe u

namespace KltDP.Manuscript.S02

section Numerical

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Manuscript, proof of Theorem 2.7: from `Hm · G_i = 0`, `Hm² > 0`, `Hm · C₀ > 0` for one curve
`C₀ ⊄ G`, and `card ι + 1 = ρ(T)`, the divisor `Hm` is nef and its degree-zero prime curves are
exactly the `G_i`. -/
theorem nef_and_nullCurves_of_numerical (T : NormalProjectiveSurface k)
    (hreg : ∀ x : T.Point, RegularPoint T.toScheme x)
    {ι : Type u} [Fintype ι] (G : ι → T.PrimeCurve) (hinj : Function.Injective G)
    (hcard : Fintype.card ι + 1 = T.picardRank)
    (Hm : CartierDivisor T.toScheme)
    (hHG : ∀ i, (G i).intersectionNumber Hm = 0)
    (hsq : 0 < T.intersectionPairing hreg Hm Hm)
    (C₀ : T.PrimeCurve) (hC₀ : ∀ i, C₀ ≠ G i) (hC₀pos : 0 < C₀.intersectionNumber Hm) :
    Positivity.IsNef T.structureMorphism (cartierDivisorInvertibleSheaf T.toScheme Hm) ∧
      ∀ C : T.PrimeCurve,
        C.restrictionDegree (cartierDivisorInvertibleSheaf T.toScheme Hm) = 0 ↔ ∃ i, C = G i := by
  classical
  letI : FiniteDimensional ℚ T.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite T hreg
  -- an ample Cartier divisor `A₀`
  obtain ⟨A, hA⟩ := T.exists_isAmple
  obtain ⟨A₀, hA₀⟩ := cartierPicardClass_surjective T.toScheme A.toPic
  have hA₀ample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf T.toScheme A₀) :=
    AmplePositivity.isAmple_of_toPic_eq hA₀.symm hA
  have hApos : ∀ C : T.PrimeCurve, 0 < C.intersectionNumber A₀ := fun C =>
    AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple T _ hA₀ample C
  -- the negative intersection matrix is a Stieltjes matrix
  set M := NullCurveIntersectionMatrix.intersectionMatrix T hreg G with hMdef
  have hMsymm : ∀ i j, M i j = M j i := by
    intro i j
    change (T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
        (T.primeCurveCartier hreg (G j)) : ℚ) =
      (T.intersectionPairing hreg (T.primeCurveCartier hreg (G j))
        (T.primeCurveCartier hreg (G i)) : ℚ)
    rw [T.intersectionPairing_symm hreg]
  set N : Matrix ι ι ℚ := -M with hNdef
  have hNpd : N.PosDef := by
    constructor
    · change (-M)ᴴ = -M
      ext i j
      change -(T.intersectionPairing hreg (T.primeCurveCartier hreg (G j))
          (T.primeCurveCartier hreg (G i)) : ℚ) =
        -(T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
          (T.primeCurveCartier hreg (G j)) : ℚ)
      rw [T.intersectionPairing_symm hreg]
    · intro a ha
      have hneg : a ⬝ᵥ (M *ᵥ a) < 0 :=
        NullCurveIntersectionMatrix.quadraticForm_neg T hreg Hm hsq G hinj hHG a ha
      rw [hNdef]
      simpa only [star_trivial, neg_mulVec, dotProduct_neg] using neg_pos.mpr hneg
  have hNoff : ∀ i j, i ≠ j → N i j ≤ 0 := by
    intro i j hij
    have hnonneg := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg
      T hreg (G i) (G j) (fun h => hij (hinj h))
    change -(T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
      (T.primeCurveCartier hreg (G j)) : ℚ) ≤ 0
    exact neg_nonpos.mpr (by exact_mod_cast hnonneg)
  -- `a_i = A₀ · G_i > 0` and `x = N⁻¹ a ≥ 0` (Lemma 2.1)
  let a : ι → ℚ := fun i => ((G i).intersectionNumber A₀ : ℚ)
  have ha : ∀ i, 0 ≤ a i := fun i => by
    show (0 : ℚ) ≤ ((G i).intersectionNumber A₀ : ℚ)
    exact_mod_cast (hApos (G i)).le
  let x : ι → ℚ := N⁻¹ *ᵥ a
  have hx : ∀ i, 0 ≤ x i :=
    KltDP.LinearAlgebra.stieltjes_inverse_mulVec_nonnegative hNpd hNoff ha
  have hNx : N *ᵥ x = a := by
    show N *ᵥ (N⁻¹ *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N
      ((Matrix.isUnit_iff_isUnit_det N).mp (KltDP.LinearAlgebra.isUnit_of_posDef hNpd)),
      Matrix.one_mulVec]
  -- the numerical class `M = A₀ + Σ x_i G_i`
  set B := T.numericalIntersectionBilinForm hreg with hBdef
  let cc : ι → T.NumericalClassGroup := fun i => DisjointNegativeCurvesRank.curveClass T hreg (G i)
  let Mnum : T.NumericalClassGroup :=
    NefNullCurveNegativeSquare.cartierClass T A₀ + ∑ i, x i • cc i
  have hdeg_cartier : ∀ (D : CartierDivisor T.toScheme) (C : T.PrimeCurve),
      T.numericalRestrictionDegree C (NefNullCurveNegativeSquare.cartierClass T D) =
        (C.intersectionNumber D : ℚ) := by
    intro D C
    rw [← DisjointNegativeCurvesRank.pairing_curveClass]
    change B (NefNullCurveNegativeSquare.cartierClass T D)
      (NefNullCurveNegativeSquare.cartierClass T (T.primeCurveCartier hreg C)) = _
    rw [NefNullCurveNegativeSquare.cartierClass_pairing, T.intersectionPairing_primeCurve hreg]
  have hdeg_curve : ∀ (i : ι) (C : T.PrimeCurve),
      T.numericalRestrictionDegree C (cc i) =
        (T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
          (T.primeCurveCartier hreg C) : ℚ) := by
    intro i C
    rw [← DisjointNegativeCurvesRank.pairing_curveClass,
      DisjointNegativeCurvesRank.curveClass_pairing]
  have hdeg_M : ∀ C : T.PrimeCurve, T.numericalRestrictionDegree C Mnum =
      (C.intersectionNumber A₀ : ℚ) + ∑ i, x i *
        (T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
          (T.primeCurveCartier hreg C) : ℚ) := by
    intro C
    simp only [Mnum, map_add, map_sum, map_smul, hdeg_cartier, hdeg_curve, smul_eq_mul]
  -- `M · G_j = 0`
  have hMG : ∀ j, T.numericalRestrictionDegree (G j) Mnum = 0 := by
    intro j
    have h1 : (N *ᵥ x) j = a j := congrFun hNx j
    have h2 : (N *ᵥ x) j = -∑ i, x i * M i j := by
      simp only [Matrix.mulVec, dotProduct, hNdef, Matrix.neg_apply]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hMsymm j i]
      ring
    rw [hdeg_M]
    change a j + ∑ i, x i * M i j = 0
    linarith
  -- `M · C > 0` for every curve outside `G`
  have hMpos : ∀ C : T.PrimeCurve, (∀ i, C ≠ G i) → 0 < T.numericalRestrictionDegree C Mnum := by
    intro C hC
    rw [hdeg_M]
    have h1 : (0 : ℚ) < (C.intersectionNumber A₀ : ℚ) := by exact_mod_cast hApos C
    have h2 : 0 ≤ ∑ i, x i *
        (T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
          (T.primeCurveCartier hreg C) : ℚ) := by
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (hx i)
      exact_mod_cast PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg
        T hreg (G i) C (fun h => hC i h.symm)
    linarith
  -- the orthogonal complement of the independent classes `[G_i]` is one-dimensional
  let W : Submodule ℚ T.NumericalClassGroup := Submodule.span ℚ (Set.range cc)
  have hW : Module.finrank ℚ W = Fintype.card ι :=
    finrank_span_eq_card (NullCurveIndependenceRank.linearIndependent T hreg Hm hsq G hinj hHG)
  have horth : Module.finrank ℚ (B.orthogonal W) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal (T.numericalIntersectionBilinForm_nondegenerate hreg)
      (T.numericalIntersectionBilinForm_isSymm hreg).isRefl W, hW]
    change T.picardRank - Fintype.card ι = 1
    omega
  have hmem : ∀ v : T.NumericalClassGroup,
      (∀ i, T.numericalRestrictionDegree (G i) v = 0) → v ∈ B.orthogonal W := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    have hk : W ≤ LinearMap.ker (B v) := by
      apply Submodule.span_le.mpr
      rintro c ⟨i, rfl⟩
      change B v (cc i) = 0
      rw [DisjointNegativeCurvesRank.pairing_curveClass]
      exact hv i
    change B w v = 0
    rw [LinearMap.BilinForm.IsSymm.eq (T.numericalIntersectionBilinForm_isSymm hreg)]
    exact hk hw
  have hHmem : NefNullCurveNegativeSquare.cartierClass T Hm ∈ B.orthogonal W :=
    hmem _ (fun i => by rw [hdeg_cartier, hHG i, Int.cast_zero])
  have hMmem : Mnum ∈ B.orthogonal W := hmem _ hMG
  have hMne : (⟨Mnum, hMmem⟩ : B.orthogonal W) ≠ 0 := by
    intro h
    have h' : Mnum = 0 := congrArg Subtype.val h
    have hpos := hMpos C₀ hC₀
    rw [h', map_zero] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨Mnum, hMmem⟩ : B.orthogonal W) hMne).mp
    horth ⟨_, hHmem⟩
  have hcM : NefNullCurveNegativeSquare.cartierClass T Hm = c • Mnum := by
    have h := congrArg Subtype.val hc
    simpa using h.symm
  have hdegHm : ∀ C : T.PrimeCurve,
      (C.intersectionNumber Hm : ℚ) = c * T.numericalRestrictionDegree C Mnum := by
    intro C
    rw [← hdeg_cartier, hcM, map_smul, smul_eq_mul]
  -- `c > 0`, from the degree on `C₀`
  have hcpos : 0 < c := by
    have h1 := hdegHm C₀
    have h2 : (0 : ℚ) < (C₀.intersectionNumber Hm : ℚ) := by exact_mod_cast hC₀pos
    have h3 := hMpos C₀ hC₀
    rw [h1] at h2
    nlinarith
  -- the two conclusions
  have hnullCurves : ∀ C : T.PrimeCurve,
      C.restrictionDegree (cartierDivisorInvertibleSheaf T.toScheme Hm) = 0 ↔ ∃ i, C = G i := by
    intro C
    rw [← C.intersectionNumber_eq_restrictionDegree]
    constructor
    · intro h0
      by_cases hC : ∃ i, C = G i
      · exact hC
      · exfalso
        push_neg at hC
        have h1 := hdegHm C
        rw [h0, Int.cast_zero] at h1
        have h3 := hMpos C hC
        have h4 : (0 : ℚ) < c * T.numericalRestrictionDegree C Mnum := mul_pos hcpos h3
        rw [← h1] at h4
        exact lt_irrefl _ h4
    · rintro ⟨i, rfl⟩
      exact hHG i
  refine ⟨?_, hnullCurves⟩
  rw [Positivity.isNef_iff_forall_primeCurve]
  intro C
  rw [← C.intersectionNumber_eq_restrictionDegree]
  by_cases hC : ∃ i, C = G i
  · obtain ⟨i, rfl⟩ := hC
    rw [hHG i]
  · push_neg at hC
    have h3 := hMpos C hC
    have h4 : (0 : ℚ) < (C.intersectionNumber Hm : ℚ) := by
      rw [hdegHm C]
      exact mul_pos hcpos h3
    exact_mod_cast h4.le

/-- **Manuscript Theorem 2.7** (`thm:numerical-contraction`, lines 560–584).

Same smooth surface `T`, canonical Cartier divisor `K_T` and SNC forest `G : ι → T.PrimeCurve` of
smooth rational curves as in Theorem 2.6, with `card ι + 1 = ρ(T)`; `B = Σ β_i G_i` with
`β_i < 1`, `H = -(K_T + B)` cleared to the Cartier divisor `Hm = m H` (`hHm`).  If `Hm · G_i = 0`
for every `i`, `Hm² > 0`, and `Hm · C₀ > 0` for one prime curve `C₀` not among the `G_i`, then `G`
has a projective contraction `f : T → Y` to a normal rank-one klt del Pezzo surface with
`K_T + B = f^*K_Y` (all the conclusions of Theorem 2.6). -/
theorem numericalRankOneContraction (p : ℕ) [CharP k p] (hp : 0 < p)
    (T : NormalProjectiveSurface k) (hreg : ∀ x : T.Point, RegularPoint T.toScheme x)
    (KT : CartierDivisor T.toScheme)
    (eKT : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2)
    {ι : Type u} [Fintype ι] (G : ι → T.PrimeCurve) (hinj : Function.Injective G)
    (hrat : ∀ i, ∃ e : (G i).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (G i).toSpec)
    (hacyclic : (curveIncidenceGraph G).IsAcyclic)
    (hpair : ∀ i j, i ≠ j → T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
      (T.primeCurveCartier hreg (G j)) ≤ 1)
    (hcard : Fintype.card ι + 1 = T.picardRank)
    (lam : ι → ℚ) (hlam : ∀ i, lam i < 1)
    (m : ℕ) (hm : 0 < m) (Hm : CartierDivisor T.toScheme)
    (hHm : T.rationalCartierToWeilHom Hm =
      -((m : ℚ) • (T.rationalCartierToWeilHom KT + ∑ i, Finsupp.single (G i) (lam i))))
    (hHG : ∀ i, (G i).intersectionNumber Hm = 0)
    (hsq : 0 < T.intersectionPairing hreg Hm Hm)
    (C₀ : T.PrimeCurve) (hC₀ : ∀ i, C₀ ≠ G i) (hC₀pos : 0 < C₀.intersectionNumber Hm) :
    ∃ (Y : NormalProjectiveSurface k) (f : T.toScheme ⟶ Y.toScheme)
      (hproper : IsProper f) (hbir : IsBirationalScheme f),
      f ≫ Y.structureMorphism = T.structureMorphism ∧ IsIso f.c ∧ IsBirational f ∧
      (∀ y : Y.toScheme, IsConnected (f.base ⁻¹' {y})) ∧
      (∀ C : T.PrimeCurve, IsExceptionalCurve f C ↔ ∃ i, C = G i) ∧
      IsKltDelPezzo Y ∧ Y.picardRank = 1 ∧
      letI : IsProper f := hproper
      letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      let KY : Y.WeilDivisor :=
        BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT)
      IsKltWithCanonicalDivisor Y KY ∧ Y.QAmple (-rationalizeWeilDivisor Y KY) ∧
      ∃ hK : Y.QCartier (rationalizeWeilDivisor Y KY),
        QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK =
          T.rationalCartierToWeilHom KT + ∑ i, Finsupp.single (G i) (lam i) := by
  obtain ⟨hnef, hnull⟩ :=
    nef_and_nullCurves_of_numerical T hreg G hinj hcard Hm hHG hsq C₀ hC₀ hC₀pos
  exact anticanonicalContraction p hp T hreg KT eKT G hinj hrat hacyclic hpair hcard lam hlam
    m hm Hm hHm hnef hsq hnull

end Numerical

end KltDP.Manuscript.S02

#print axioms KltDP.Manuscript.S02.numericalRankOneContraction
