import KltDP.Examples.FrobeniusMultiCentreExceptional

/-!
# Bundle: the exceptional configuration of `S_{p,n}` as actual closed subschemes

`sPn_exceptional_configuration` collects, for an algebraically closed field `k`, `p = q + 1`, and
an injective selection `a : Fin n → k`, the facts proved about the `n·p` exceptional curves
`exceptionalCurve q n a i idx` of the multi-centre surface `S_{p,n} = multiSurface (q+1) n a`
(`idx = Sum.inl j` is `C_{i,j+1}`, `idx = Sum.inr _` is `P_i = E_{ip}`):

1. each is a closed subscheme of `S_{p,n}` (closed immersion `exceptionalCurveι`), and its
   comparison map to the accepted exceptional component of the `i`-th tower is an isomorphism;
2. `P_i ≅ P¹` and `P_i` is integral; each `C_{ij}` is reduced and isomorphic to the accepted whole
   strict transform of the exceptional curve of the `i`-th tower;
3. every point of `E_{i,idx}` projects to the `i`-th centre, the supports are closed, and curves of
   different towers are disjoint;
4. inside one tower: non-adjacent `C_{ij}` are disjoint, `P_i` is disjoint from every `C_{ij}` with
   `j + 1 < q`, adjacent `C_{i,j+1}` and `C_{i,j+2}` meet, and `C_{i,q}` meets `P_i`.

Not part of this bundle (not proved): `C_{ij} ≅ P¹`, single-point intersections, the strict
transforms `B` and `F_i` in `S_{p,n}` and their contacts, hence the full reduced divisor `D`; see
`F29_CONFIGURATION.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusTranslatedCharts
  FrobeniusGlobalExceptionalSuccessor FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional

/-- The exceptional configuration of `S_{p,n}` (`p = q + 1`): the clauses proved so far. -/
theorem sPn_exceptional_configuration (k : Type u) [Field k] [IsAlgClosed k]
    (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    -- (1) closed subschemes, isomorphic to the accepted tower components
    (∀ (i : Fin n) (idx : FinalIndex.{0} q), IsClosedImmersion (exceptionalCurveι q n a i idx)) ∧
    (∀ (i : Fin n) (idx : FinalIndex.{0} q), IsIso (exceptionalCurveToComponent q n a i idx)) ∧
    (∀ (i : Fin n) (idx : FinalIndex.{0} q),
        exceptionalCurveι q n a i idx ≫ towerProjection (q + 1) n a i =
          exceptionalCurveToComponent q n a i idx ≫
            finalComponentι (translatedInitial (q + 1) (a i)) q idx) ∧
    -- (2) `P_i ≅ P¹`, integral; `C_{ij}` reduced, isomorphic to the accepted strict transform
    (∀ i : Fin n, Nonempty (exceptionalCurve q n a i (Sum.inr PUnit.unit) ≅ projectiveSpace k 1)) ∧
    (∀ i : Fin n, IsIntegral (exceptionalCurve q n a i (Sum.inr PUnit.unit))) ∧
    (∀ (i : Fin n) (j : Fin q), IsReduced (exceptionalCurve q n a i (Sum.inl j))) ∧
    (∀ (i : Fin n) (j : Fin q), Nonempty (exceptionalCurve q n a i (Sum.inl j) ≅
        previousStrictTransform ((translatedInitial (q + 1) (a i)).stage j.val))) ∧
    -- (3) supports: closed, over the centre, disjoint across towers
    (∀ (i : Fin n) (idx : FinalIndex.{0} q), IsClosed (exceptionalSupport q n a i idx)) ∧
    (∀ (i : Fin n) (idx : FinalIndex.{0} q) (x : multiSurface (q + 1) n a),
        x ∈ exceptionalSupport q n a i idx →
          (multiProjection (q + 1) n a).base x = graphPoint (q + 1) (a i)) ∧
    (∀ (i i' : Fin n) (idx idx' : FinalIndex.{0} q), i ≠ i' →
        Disjoint (exceptionalSupport q n a i idx) (exceptionalSupport q n a i' idx')) ∧
    -- (4) incidences inside one tower
    (∀ (i : Fin n) (j j' : Fin q), j.val + 1 < j'.val →
        Disjoint (exceptionalSupport q n a i (Sum.inl j)) (exceptionalSupport q n a i (Sum.inl j'))) ∧
    (∀ (i : Fin n) (j : Fin q), j.val + 1 < q →
        Disjoint (exceptionalSupport q n a i (Sum.inl j))
          (exceptionalSupport q n a i (Sum.inr PUnit.unit))) ∧
    (∀ (i : Fin n) (j : ℕ) (hj : j + 1 < q),
        (exceptionalSupport q n a i (Sum.inl ⟨j, by omega⟩) ∩
          exceptionalSupport q n a i (Sum.inl ⟨j + 1, hj⟩)).Nonempty) ∧
    (∀ (m : ℕ) (hq : q = m + 1) (i : Fin n),
        (exceptionalSupport q n a i (Sum.inl ⟨m, by omega⟩) ∩
          exceptionalSupport q n a i (Sum.inr PUnit.unit)).Nonempty) :=
  ⟨fun i idx => exceptionalCurveι_isClosedImmersion q n a i idx,
    fun i idx => exceptionalCurveToComponent_isIso q n a ha i idx,
    fun i idx => exceptionalCurve_condition q n a i idx,
    fun i => ⟨newestCurveIso q n a ha i⟩,
    fun i => newestCurve_isIntegral q n a ha i,
    fun i j => olderCurve_isReduced q n a ha i j,
    fun i j => ⟨exceptionalCurveIso q n a ha i (Sum.inl j)⟩,
    fun i idx => exceptionalSupport_isClosed q n a i idx,
    fun i idx x hx => exceptionalSupport_projection q n a i idx x hx,
    fun i i' idx idx' h => exceptionalSupport_disjoint_of_ne q n a ha h idx idx',
    fun i j j' h => exceptionalSupport_disjoint_nonadjacent q n a i j j' h,
    fun i j h => exceptionalSupport_disjoint_newest q n a i j h,
    fun i j hj => exceptionalSupport_adjacent q n a ha i j hj,
    fun m hq i => by
      subst hq
      exact exceptionalSupport_last_adjacent m n a ha i⟩

/-- The bundle has exactly one universe parameter. -/
theorem sPn_exceptional_configuration_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) : True := by
  have _ := sPn_exceptional_configuration.{u} k q n a ha
  trivial

end KltDP.Examples
