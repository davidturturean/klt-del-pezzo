import KltDP.Examples.FrobeniusStageNoetherianFiniteType

/-!
# Integral Picard divisibility on the exceptional chain (the §10/§12 consumer of Lemma 2.2)

BRIEF20, task 3. The manuscript uses `lem:tree-picard` (`source/manuscript.tex` 367–373) in the
following form: on a connected rational tree `Z` of exceptional curves, a line bundle whose
multidegree is divisible by `d` is `d` times a class, and in particular a line bundle of
multidegree zero is trivial ("a divisible multiple restricts trivially to `D`", line 448; "the
restriction of `M` has degree zero on every irreducible component, hence is trivial", line 1324;
"on a disjoint original rational tree the half-class has multidegree zero and is trivial", lines
3111–3113, the Frobenius family). Here `Z` is the exceptional chain `C_1 ∪ ⋯ ∪ C_q ∪ P` of a
contact tower (BRIEF19's `chainScheme q A`) and the class comes from the ambient stage by pullback
along the closed immersion `chainInclusion q A`.

* `exists_pow_of_dvd_multidegree` (generic): when the multidegree map of `X` is bijective, a
  Picard class whose multidegree is divisible by `d` on every component is a `d`-th power.
* `chain_pullback_pow_of_dvd`: for a Picard class `L` of the stage `A_{q+1}` whose pullback to the
  chain has multidegree divisible by `d` on every curve, the pullback is `M ^ d` for a class `M` of
  the chain; `chain_pullback_toPic_pow_of_dvd_exponent` is the same statement for an actual line
  bundle `L` with the hypothesis on the component exponents of `pullbackInvertibleSheaf`; the
  multidegree-zero clause is BRIEF19's `chain_trivial_of_degree_zero`.

Hypotheses still carried (recorded): `ChainSinglePoints q A` and `ChainTransversal q A hyp` — lane
F's chain transversality (adjacent exceptional curves meet transversally in exactly one point);
the Noetherian and finite-type hypotheses on the stage are discharged by task 1 (charted plane with
Noetherian carrier proper over `k`; in particular the Frobenius contact tower). The degree is the
transition exponent `componentExponent` (its comparison with a divisor degree is a separate
obligation, `LEMMA22_PROGRESS.md` gap item 6).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable {k : Type u} [Field k] (X : Scheme.{u}) [NoetherianSpace X]
  (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)

/-- **Divisibility.** If the multidegree map is bijective, a Picard class whose multidegree is
divisible by `d` on every component is the `d`-th power of a class. -/
theorem exists_pow_of_dvd_multidegree (hbij : Function.Bijective (multidegreeHom k X e))
    (p : X.Pic) (d : ℕ)
    (hd : ∀ C, (d : ℤ) ∣ Multiplicative.toAdd (multidegreeHom k X e p C)) :
    ∃ M : X.Pic, p = M ^ d := by
  obtain ⟨M, hM⟩ := hbij.2
    (fun C => Multiplicative.ofAdd (Multiplicative.toAdd (multidegreeHom k X e p C) / (d : ℤ)))
  refine ⟨M, hbij.1 ?_⟩
  rw [map_pow, hM]
  funext C
  simp only [Pi.pow_apply, ← ofAdd_nsmul, nsmul_eq_mul, Int.mul_ediv_cancel' (hd C), ofAdd_toAdd]

end KltDP.Geometry.RationalTreePicard

namespace KltDP.Examples.FrobeniusExceptionalChainDivisibility

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalChainPicard
  FrobeniusStageNoetherianFiniteType

variable {k : Type u} [Field k] [IsAlgClosed k] (A : PlaneChartedScheme k)
  [NoetherianSpace A.carrier] [IsLocallyNoetherian A.carrier] [IsProper A.structureMap] (q : ℕ)
  (hyp : ChainSinglePoints q A) (htrans : ChainTransversal q A hyp)

include htrans in
/-- **Integral Picard divisibility on the exceptional chain.** A Picard class `L` of the stage
`A_{q+1}` whose pullback to the exceptional chain `C_1 ∪ ⋯ ∪ C_q ∪ P` has multidegree divisible by
`d` on every curve pulls back to the `d`-th power of a class of the chain. -/
theorem chain_pullback_pow_of_dvd (L : (chainStage q A).Pic) (d : ℕ)
    (hd : ∀ idx : FinalIndex.{u} q, (d : ℤ) ∣ Multiplicative.toAdd
      (multidegreeHom k (chainScheme q A)
        (lineIdentification (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
          (chainCurve_distinct q A hyp))
        (schemePicardPullbackHom (chainInclusion q A) L)
        (lineComponent (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
          (chainCurve_distinct q A hyp) idx))) :
    ∃ M : (chainScheme q A).Pic, schemePicardPullbackHom (chainInclusion q A) L = M ^ d := by
  apply exists_pow_of_dvd_multidegree (chainScheme q A) _
    (chain_rationalTreePicard_of_tower A q hyp htrans)
  intro C
  obtain ⟨idx, rfl⟩ := lineComponent_surjective (chainScheme q A) (chainCurve q A)
    (chainCurve_cover q A) (chainCurve_distinct q A hyp) C
  exact hd idx

include htrans in
/-- The same for an actual line bundle `L` on the stage, with the hypothesis on the component
exponents of its pullback to the chain: the class of the pullback is a `d`-th power. -/
theorem chain_pullback_toPic_pow_of_dvd_exponent (L : InvertibleSheaf (chainStage q A)) (d : ℕ)
    (hd : ∀ idx : FinalIndex.{u} q, (d : ℤ) ∣ componentExponent k (chainScheme q A)
      {lineComponent (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
        (chainCurve_distinct q A hyp) idx}
      (lineIdentification (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
        (chainCurve_distinct q A hyp)
        (lineComponent (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
          (chainCurve_distinct q A hyp) idx))
      (pullbackInvertibleSheaf (chainInclusion q A) L)) :
    ∃ M : (chainScheme q A).Pic,
      (pullbackInvertibleSheaf (chainInclusion q A) L).toPic = M ^ d := by
  apply exists_pow_of_dvd_multidegree (chainScheme q A) _
    (chain_rationalTreePicard_of_tower A q hyp htrans)
  intro C
  obtain ⟨idx, rfl⟩ := lineComponent_surjective (chainScheme q A) (chainCurve q A)
    (chainCurve_cover q A) (chainCurve_distinct q A hyp) C
  simp only [multidegreeHom_toPic, toAdd_ofAdd]
  exact hd idx

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (A₀ : PlaneChartedScheme k₀)
    [NoetherianSpace A₀.carrier] [IsLocallyNoetherian A₀.carrier] [IsProper A₀.structureMap]
    (q₀ : ℕ) (hyp : ChainSinglePoints q₀ A₀) (htrans : ChainTransversal q₀ A₀ hyp)
    (L : (chainStage q₀ A₀).Pic) (d : ℕ)
    (hd : ∀ idx : FinalIndex.{0} q₀, (d : ℤ) ∣ Multiplicative.toAdd
      (multidegreeHom k₀ (chainScheme q₀ A₀)
        (lineIdentification (chainScheme q₀ A₀) (chainCurve q₀ A₀) (chainCurve_cover q₀ A₀)
          (chainCurve_distinct q₀ A₀ hyp))
        (schemePicardPullbackHom (chainInclusion q₀ A₀) L)
        (lineComponent (chainScheme q₀ A₀) (chainCurve q₀ A₀) (chainCurve_cover q₀ A₀)
          (chainCurve_distinct q₀ A₀ hyp) idx))) :
    ∃ M : (chainScheme q₀ A₀).Pic, schemePicardPullbackHom (chainInclusion q₀ A₀) L = M ^ d :=
  chain_pullback_pow_of_dvd A₀ q₀ hyp htrans L d hd

end KltDP.Examples.FrobeniusExceptionalChainDivisibility
