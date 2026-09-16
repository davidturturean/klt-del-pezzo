import KltDP.Examples.FrobeniusExceptionalChainDivisibility
import KltDP.Examples.RationalTreePicardWitnessTwoFibresCrossing

/-!
# The half-class clause of Lemma 2.2 (manuscript lines 3105–3115, parity argument)

BRIEF22, task 2. In the characteristic-two corollary the manuscript writes: "for distinct indices
`i, j` there is the explicit even set `F_i + U_i + F_j + U_j ∼ 2(b − P_i − P_j)`", and, for the
half-class `H = b − P_i − P_j`, "on a disjoint original rational tree the half-class has
multidegree zero and is trivial by `lem:tree-picard`". The clause used is therefore:

* (torsion-freeness) on a rational tree `Z` the multidegree map is bijective, so a class whose
  `d`-th power is trivial is trivial (`eq_one_of_pow_eq_one_of_bijective_multidegree`), in
  particular a class whose square is trivial (`eq_one_of_sq_eq_one_of_bijective_multidegree`);
* (half-class) for a class `M` of the ambient surface whose double restricts trivially to `Z`
  (the even set is disjoint from `Z`), or whose double has multidegree zero on every component
  of `Z`, the restriction of `M` to `Z` is trivial (`pullback_eq_one_of_pullback_sq_eq_one`,
  `pullback_eq_one_of_multidegree_sq_eq_one`);
* (even degrees ⇒ square) a class with even multidegree on every component is a square
  (`exists_sq_of_even_multidegree`, the `d = 2` case of the task-20 divisibility).

These are instantiated on the exceptional chain `C_1 ∪ ⋯ ∪ C_q ∪ P` of a tower over a Noetherian
charted plane proper over `k` (`chain_pullback_sq_of_even`, `chain_halfClass_trivial`,
`chain_halfClass_trivial_of_multidegree`; hypotheses `ChainSinglePoints`, `ChainTransversal` as
in tasks 19–20) and on witness (b), the two fibres `x = 0 ∪ y = 0` of `P¹ × P¹`
(`twoFibres_halfClass_trivial`, unconditional). The identification of `componentExponent` with
the intersection-theoretic degree, and the vanishing of the restriction of a divisor class to a
curve disjoint from its support, are separate obligations (gap item 6); here "the even set is
disjoint from `Z`" enters as the hypothesis that its class restricts trivially.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable {k : Type u} [Field k] (X : Scheme.{u}) [NoetherianSpace X]
  (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)

/-- **Torsion-freeness.** If the multidegree map is bijective, a Picard class with trivial `d`-th
power (`d ≠ 0`) is trivial. -/
theorem eq_one_of_pow_eq_one_of_bijective_multidegree
    (hbij : Function.Bijective (multidegreeHom k X e)) (p : X.Pic) (d : ℕ) (hd : d ≠ 0)
    (hp : p ^ d = 1) : p = 1 := by
  apply hbij.1
  rw [map_one]
  funext C
  have h := congrArg (fun q => multidegreeHom k X e q C) hp
  simp only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] at h
  have h' : d • Multiplicative.toAdd (multidegreeHom k X e p C) = 0 := by
    rw [← toAdd_pow, h, toAdd_one]
  rcases smul_eq_zero.mp h' with h0 | h0
  · exact absurd h0 hd
  · exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)

/-- A Picard class of a rational tree whose square is trivial is trivial. -/
theorem eq_one_of_sq_eq_one_of_bijective_multidegree
    (hbij : Function.Bijective (multidegreeHom k X e)) (p : X.Pic) (hp : p ^ 2 = 1) : p = 1 :=
  eq_one_of_pow_eq_one_of_bijective_multidegree X e hbij p 2 two_ne_zero hp

/-- **Even degrees give a square.** -/
theorem exists_sq_of_even_multidegree (hbij : Function.Bijective (multidegreeHom k X e))
    (p : X.Pic) (hp : ∀ C, Even (Multiplicative.toAdd (multidegreeHom k X e p C))) :
    ∃ M : X.Pic, p = M ^ 2 :=
  exists_pow_of_dvd_multidegree X e hbij p 2 fun C => by
    rw [Nat.cast_ofNat]
    exact even_iff_two_dvd.mp (hp C)

variable {S : Scheme.{u}} (ι : X ⟶ S)

/-- **The half-class clause.** A class `M` of the ambient scheme whose double restricts trivially
to the rational tree `X` restricts trivially. -/
theorem pullback_eq_one_of_pullback_sq_eq_one (hbij : Function.Bijective (multidegreeHom k X e))
    (M : S.Pic) (h : schemePicardPullbackHom ι (M ^ 2) = 1) :
    schemePicardPullbackHom ι M = 1 :=
  eq_one_of_sq_eq_one_of_bijective_multidegree X e hbij _ (by rw [← map_pow]; exact h)

/-- The half-class clause in multidegree form: if the double of `M` has multidegree zero on every
component of the tree, the restriction of `M` is trivial. -/
theorem pullback_eq_one_of_multidegree_sq_eq_one
    (hbij : Function.Bijective (multidegreeHom k X e)) (M : S.Pic)
    (h : ∀ C, multidegreeHom k X e (schemePicardPullbackHom ι (M ^ 2)) C = 1) :
    schemePicardPullbackHom ι M = 1 := by
  apply pullback_eq_one_of_pullback_sq_eq_one X e ι hbij M
  apply hbij.1
  rw [map_one]
  funext C
  exact h C

end KltDP.Geometry.RationalTreePicard

namespace KltDP.Examples.FrobeniusExceptionalHalfClass

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalChainPicard
  FrobeniusStageNoetherianFiniteType FrobeniusExceptionalChainDivisibility

variable {k : Type u} [Field k] [IsAlgClosed k]

section Chain

variable (A : PlaneChartedScheme k) [NoetherianSpace A.carrier] [IsLocallyNoetherian A.carrier]
  [IsProper A.structureMap] (q : ℕ) (hyp : ChainSinglePoints q A) (htrans : ChainTransversal q A hyp)

include htrans in
/-- **Even exceptional degrees give a square on the chain**: a class of the stage `A_{q+1}` whose
pullback to the exceptional chain has even multidegree on every curve pulls back to a square. -/
theorem chain_pullback_sq_of_even (L : (chainStage q A).Pic)
    (hd : ∀ idx : FinalIndex.{u} q, Even (Multiplicative.toAdd
      (multidegreeHom k (chainScheme q A)
        (lineIdentification (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
          (chainCurve_distinct q A hyp))
        (schemePicardPullbackHom (chainInclusion q A) L)
        (lineComponent (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
          (chainCurve_distinct q A hyp) idx)))) :
    ∃ M : (chainScheme q A).Pic, schemePicardPullbackHom (chainInclusion q A) L = M ^ 2 :=
  chain_pullback_pow_of_dvd A q hyp htrans L 2 fun idx => by
    rw [Nat.cast_ofNat]
    exact even_iff_two_dvd.mp (hd idx)

include htrans in
/-- **The half-class clause on the chain**: a class `M` of the stage whose double restricts
trivially to the exceptional chain restricts trivially. -/
theorem chain_halfClass_trivial (M : (chainStage q A).Pic)
    (h : schemePicardPullbackHom (chainInclusion q A) (M ^ 2) = 1) :
    schemePicardPullbackHom (chainInclusion q A) M = 1 :=
  pullback_eq_one_of_pullback_sq_eq_one (chainScheme q A) _ (chainInclusion q A)
    (chain_rationalTreePicard_of_tower A q hyp htrans) M h

include htrans in
/-- The same with the hypothesis that the double of `M` has multidegree zero on every exceptional
curve ("the half-class has multidegree zero and is trivial"). -/
theorem chain_halfClass_trivial_of_multidegree (M : (chainStage q A).Pic)
    (h : ∀ idx : FinalIndex.{u} q, multidegreeHom k (chainScheme q A)
      (lineIdentification (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
        (chainCurve_distinct q A hyp))
      (schemePicardPullbackHom (chainInclusion q A) (M ^ 2))
      (lineComponent (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
        (chainCurve_distinct q A hyp) idx) = 1) :
    schemePicardPullbackHom (chainInclusion q A) M = 1 := by
  apply pullback_eq_one_of_multidegree_sq_eq_one (chainScheme q A) _ (chainInclusion q A)
    (chain_rationalTreePicard_of_tower A q hyp htrans) M
  intro C
  obtain ⟨idx, rfl⟩ := lineComponent_surjective (chainScheme q A) (chainCurve q A)
    (chainCurve_cover q A) (chainCurve_distinct q A hyp) C
  exact h idx

end Chain

section TwoFibres

open RationalTreePicardWitnessTwoFibres

/-- The half-class clause on witness (b), unconditionally: a class of `P¹ × P¹` whose double
restricts trivially to `x = 0 ∪ y = 0` restricts trivially. -/
theorem twoFibres_halfClass_trivial (M : (FrobeniusProjectivePoints.projectiveProduct k).Pic)
    (h : schemePicardPullbackHom (twoFibresInclusion (k := k)) (M ^ 2) = 1) :
    schemePicardPullbackHom (twoFibresInclusion (k := k)) M = 1 :=
  pullback_eq_one_of_pullback_sq_eq_one (twoFibresScheme (k := k)) _ (twoFibresInclusion (k := k))
    (twoFibres_rationalTreePicard' (k := k)) M h

end TwoFibres

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (A₀ : PlaneChartedScheme k₀)
    [NoetherianSpace A₀.carrier] [IsLocallyNoetherian A₀.carrier] [IsProper A₀.structureMap]
    (q₀ : ℕ) (hyp : ChainSinglePoints q₀ A₀) (htrans : ChainTransversal q₀ A₀ hyp)
    (M : (chainStage q₀ A₀).Pic)
    (h : schemePicardPullbackHom (chainInclusion q₀ A₀) (M ^ 2) = 1) :
    schemePicardPullbackHom (chainInclusion q₀ A₀) M = 1 :=
  chain_halfClass_trivial A₀ q₀ hyp htrans M h

end KltDP.Examples.FrobeniusExceptionalHalfClass
