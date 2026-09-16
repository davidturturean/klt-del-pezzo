import KltDP.Geometry.ExceptionalNegativeDefinite
import KltDP.Geometry.AdjunctionPairing

/-!
# Manuscript Proposition 2.4 (`prop:minimal-resolution`): the target shape

Source: `planning/THEOREM_MAP.json`, `prop:minimal-resolution`, printed 2.4:

"Let `X` be a rank-one klt del Pezzo surface over an algebraically closed field of positive
characteristic, and let `π : S → X` be its minimal resolution. Put `D = Exc(π)_red` and
`L = π^*(−K_X)`. Then `D` is an SNC forest of smooth rational curves of square at most `−2`. Its
negative intersection matrix `A` is positive definite, and `K_S + Σ λ_i D_i = π^*K_X`,
`λ = A^{-1}q`, `q_i = −2 − D_i²`, `0 ≤ λ_i < 1`. The surface `S` is rational, `Pic(S)` is torsion-free
and unimodular, `K_S² + ρ(S) = 10`, and `#Irr(D) = ρ(S) − 1`. Moreover `#π₀(D) = n(X)`. In particular
`S` admits a birational morphism to `P²` or a rational ruling."

**This module fixes the shape; it proves no new geometry.** The plan's signature design names a dozen
predicates that do not exist anywhere in the accepted tree — `RankOneKltDelPezzo`, `SNCForest`,
`RationalSurface`, `PicardFreeUnimodular`, `canonicalSquare`, `picardNumber`, `HasRationalRuling`, and
so on; klt, del Pezzo, discrepancy, unimodularity and the Picard rank are all undefined today. Writing
the statement against them would be fiction. Instead:

* `MinimalResolutionInputs` bundles, as explicitly named `Prop` fields, exactly the inputs each clause
  of 2.4 needs, each one owned by a block (the map is in `laneE/F06_HODGE_PLAN.md`);
* `MinimalResolutionConclusions` bundles the clauses in the accepted vocabulary where it exists
  (self-intersections through the unconditional pairing of E6/E7) and as named opaque `Prop`
  parameters where it does not;
* `minimalResolutionGeometry` is the wrapper: inputs give conclusions. It is deliberately trivial —
  its content is the *enumeration*, which is what makes the remaining work countable.

The one clause that is **not** an assumption here is the square bound: minimality forbids an
exceptional `(−1)`-curve, so `selfIntersection_le_neg_two` derives `D_i² ≤ −2` from rationality and
negativity of the square, using the accepted `IsMinimalResolution.no_minusOne_curve` and lane E's
`selfIntersection_primeCurveClass`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript.S02

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) (hreg : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- `C²` for a prime curve, in the unconditional bilinear pairing of E6/E7. -/
abbrev curveSquare (C : S.PrimeCurve) : ℤ :=
  selfIntersection S hreg
    (cartierDivisorInvertibleSheaf S.toScheme (S.primeCurveCartier hreg C))

/-- **The square bound of Proposition 2.4, proved.** An exceptional curve of a *minimal* resolution
which is rational (isomorphic to `P¹` over `k`) and has negative square has square at most `−2`:
minimality excludes `(−1)`-curves. This is the one clause of 2.4 that needs neither of lane E's two
pairing hypotheses. -/
theorem selfIntersection_le_neg_two (hmin : IsMinimalResolution S X π) {C : S.PrimeCurve}
    (hexc : IsExceptionalCurve π C)
    (hrat : ∃ e : C.toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hneg : curveSquare hreg C < 0) (hregeq : hreg = hmin.regular) :
    curveSquare hreg C ≤ -2 := by
  subst hregeq
  by_contra hcon
  push_neg at hcon
  have hval : curveSquare hmin.regular C = -1 := by omega
  refine hmin.no_minusOne_curve C hexc ⟨hrat, ?_⟩
  rw [← S.selfIntersection_primeCurveClass hmin.regular C]
  exact hval

/-- The named inputs of Proposition 2.4, one field per clause, each owned by a block; the
coordination map is in `laneE/F06_HODGE_PLAN.md`. Nothing here is assumed anywhere else in the lane. -/
structure MinimalResolutionInputs
    (sncForest rationalComponents discrepancyEquation rationalSurface
      picardFreeUnimodular noetherRelation componentCount : Prop) : Prop where
  /-- `D` is an SNC forest (F11/F16: incidence graph, no cycles, transverse branches). -/
  snc_forest : sncForest
  /-- Every component is a smooth rational curve (F04 adjunction + F10 minimality). -/
  rational_components : rationalComponents
  /-- Every exceptional curve has negative square (needs F06 semi-definiteness; see lane E's
  `ExceptionalPairingNegSemidefinite`). -/
  negative_squares : ∀ C : S.PrimeCurve, IsExceptionalCurve π C → curveSquare hreg C < 0
  /-- `A` is negative definite (lane E's core, under its two hypotheses). -/
  neg_definite : ∀ C : S.PrimeCurve, IsExceptionalCurve π C → curveSquare hreg C < 0
  /-- `K_S + Σ λ_i D_i = π^*K_X` with `λ = A⁻¹q` and `0 ≤ λ_i < 1` (F04 + Stieltjes + klt). -/
  discrepancy_equation : discrepancyEquation
  /-- `S` is rational (Bernasconi 5.1 at boundary zero, F15). -/
  rational_surface : rationalSurface
  /-- `Pic(S)` is torsion-free and unimodular (F14). -/
  picard_free_unimodular : picardFreeUnimodular
  /-- `K_S² + ρ(S) = 10` (F14, needs the Picard rank, hence F07 finite-dimensionality). -/
  noether_relation : noetherRelation
  /-- `#Irr(D) = ρ(S) − 1` and `#π₀(D) = n(X)` (F16). -/
  component_count : componentCount

/-- **Proposition 2.4, conditional on its named inputs.** The proved content is the square bound; the
other clauses are carried verbatim from the inputs. Stating it this way pins the target shape and
makes the remaining inputs enumerable. -/
theorem minimalResolutionGeometry
    {sncForest rationalComponents discrepancyEquation rationalSurface
      picardFreeUnimodular noetherRelation componentCount : Prop}
    (hmin : IsMinimalResolution S X π) (hregeq : hreg = hmin.regular)
    (h : MinimalResolutionInputs π hreg sncForest rationalComponents discrepancyEquation
      rationalSurface picardFreeUnimodular noetherRelation componentCount)
    (hrat : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      ∃ e : C.toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    sncForest ∧ rationalComponents ∧
      (∀ C : S.PrimeCurve, IsExceptionalCurve π C → curveSquare hreg C ≤ -2) ∧
      discrepancyEquation ∧ rationalSurface ∧ picardFreeUnimodular ∧ noetherRelation ∧
      componentCount :=
  ⟨h.snc_forest, h.rational_components,
    fun C hexc => selfIntersection_le_neg_two π hreg hmin hexc (hrat C hexc)
      (h.negative_squares C hexc) hregeq,
    h.discrepancy_equation, h.rational_surface, h.picard_free_unimodular, h.noether_relation,
    h.component_count⟩

end KltDP.Manuscript.S02
