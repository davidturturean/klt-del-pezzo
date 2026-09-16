import KltDP.Examples.FrobeniusMultiCentreChainPicard
import KltDP.Examples.FrobeniusExceptionalHalfClass

/-!
# The half-class clause on the exceptional chains of `S_{p,n}`

BRIEF22, task 2 on the multi-centre surface. For a Picard class `L` of `S_{p,n}` whose degree
(component exponent) on every curve of the `i`-th exceptional chain is even, the restriction of
`L` to that chain is a square (`towerChain_pullback_sq_of_even`); a class `M` whose double
restricts trivially to the chain — the manuscript's half-class `b − P_i − P_j` of the even set
`F_i + U_i + F_j + U_j`, disjoint from the chain — restricts trivially
(`towerChain_halfClass_trivial`, and the multidegree form
`towerChain_halfClass_trivial_of_multidegree`). Hypotheses as in `FrobeniusMultiCentreChainPicard`:
`k` algebraically closed, `a` injective, lane F's `SinglePoints` and `TowerTransversal`. The
statement for the whole exceptional locus (all `n` chains at once) needs its Picard group, i.e.
the disjoint-union step recorded there.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreHalfClass

open KltDP.Geometry KltDP.Geometry.RationalTreePicard FrobeniusMultiCentreSurface
  FrobeniusMultiCentreChainPicard

variable {k : Type u} [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
  (ha : Function.Injective a) (hyp : SinglePoints q n a) (htrans : TowerTransversal q n a ha hyp)

/-- The multidegree of the `i`-th exceptional chain of `S_{p,n}`. -/
abbrev towerMultidegree (i : Fin n) :
    (towerChain q n a ha i).Pic →*
      (↥(irreducibleComponents (towerChain q n a ha i)) → Multiplicative ℤ) :=
  multidegreeHom k (towerChain q n a ha i)
    (lineIdentification (towerChain q n a ha i)
      (CurveChain.curve (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
      (CurveChain.curve_cover (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
      (CurveChain.curve_distinct (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
        (chainData q n a ha hyp i)))

include htrans in
/-- **Even exceptional degrees give a square on the chain.** -/
theorem towerChain_pullback_sq_of_even (i : Fin n) (L : (multiSurface (q + 1) n a).Pic)
    (hd : ∀ C, Even (Multiplicative.toAdd (towerMultidegree q n a ha hyp i
      (schemePicardPullbackHom (towerChainInclusion q n a ha i) L) C))) :
    ∃ M : (towerChain q n a ha i).Pic,
      schemePicardPullbackHom (towerChainInclusion q n a ha i) L = M ^ 2 :=
  exists_sq_of_even_multidegree (towerChain q n a ha i) _
    (towerChain_rationalTreePicard q n a ha hyp htrans i) _ hd

include htrans in
/-- **The half-class clause on the chain**: a class whose double restricts trivially to the `i`-th
exceptional chain restricts trivially. -/
theorem towerChain_halfClass_trivial (i : Fin n) (M : (multiSurface (q + 1) n a).Pic)
    (h : schemePicardPullbackHom (towerChainInclusion q n a ha i) (M ^ 2) = 1) :
    schemePicardPullbackHom (towerChainInclusion q n a ha i) M = 1 :=
  pullback_eq_one_of_pullback_sq_eq_one (towerChain q n a ha i) _ (towerChainInclusion q n a ha i)
    (towerChain_rationalTreePicard q n a ha hyp htrans i) M h

include htrans in
/-- The half-class clause in multidegree form. -/
theorem towerChain_halfClass_trivial_of_multidegree (i : Fin n) (M : (multiSurface (q + 1) n a).Pic)
    (h : ∀ C, towerMultidegree q n a ha hyp i
      (schemePicardPullbackHom (towerChainInclusion q n a ha i) (M ^ 2)) C = 1) :
    schemePicardPullbackHom (towerChainInclusion q n a ha i) M = 1 :=
  pullback_eq_one_of_multidegree_sq_eq_one (towerChain q n a ha i) _
    (towerChainInclusion q n a ha i) (towerChain_rationalTreePicard q n a ha hyp htrans i) M h

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (q₀ n₀ : ℕ) (a₀ : Fin n₀ → k₀)
    (ha₀ : Function.Injective a₀) (hyp : SinglePoints q₀ n₀ a₀)
    (htrans : TowerTransversal q₀ n₀ a₀ ha₀ hyp) (i : Fin n₀) (M : (multiSurface (q₀ + 1) n₀ a₀).Pic)
    (h : schemePicardPullbackHom (towerChainInclusion q₀ n₀ a₀ ha₀ i) (M ^ 2) = 1) :
    schemePicardPullbackHom (towerChainInclusion q₀ n₀ a₀ ha₀ i) M = 1 :=
  towerChain_halfClass_trivial q₀ n₀ a₀ ha₀ hyp htrans i M h

end KltDP.Examples.FrobeniusMultiCentreHalfClass
