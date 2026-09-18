import KltDP.Geometry.FiniteDisjointCurveIntersectionContractions
import KltDP.Geometry.GeneralMinimalResolutionExistence
import KltDP.Geometry.NullCurveIntersectionMatrix

/-!
# The same blowdowns preserve an arbitrary surviving curve family

Actual finite disjoint minus-one curves produce one sequence of blowdowns.
An arbitrary indexed family of original curves avoiding those curves has
actual target image primes, with the original curve isomorphisms and maps.
The entire original intersection matrix is literally preserved. The
surviving family need not be pairwise disjoint, finite, or injective.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u v w

namespace KltDP.Geometry

/-- Construct the target family and its full matrix through the same actual blowdown morphism. -/
theorem exists_blowdowns_with_surviving_family
    {k : Type u} [Field k] [IsAlgClosed k] {ι : Type v} [Finite ι] {κ : Type w}
    (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) (E : ι → S.PrimeCurve)
    (hminus : ∀ i, IsMinusOneCurve hS (E i))
    (hpair : Pairwise (fun i j => Disjoint (E i : Set S.toScheme) (E j : Set S.toScheme)))
    (Q : κ → S.PrimeCurve)
    (havoid : ∀ j i, Disjoint (Q j : Set S.toScheme) (E i : Set S.toScheme)) :
    ∃ (T : NormalProjectiveSurface k)
      (hT : ∀ t : T.Point, RegularPoint T.toScheme t) (b : S.toScheme ⟶ T.toScheme)
      (Q' : κ → T.PrimeCurve),
      IsPointBlowupSequence S T b ∧ (∀ i, IsExceptionalCurve b (E i)) ∧
      (∀ j, b.base '' (Q j : Set S.toScheme) = (Q' j : Set T.toScheme) ∧
        ∃ η : (Q' j).toScheme ≅ (Q j).toScheme,
          η.hom ≫ ((Q j).inclusion ≫ b) = (Q' j).inclusion ∧
          η.hom ≫ (Q j).toSpec = (Q' j).toSpec ∧
          (Q' j).selfIntersectionNumber hT = (Q j).selfIntersectionNumber hS) ∧
      NullCurveIntersectionMatrix.intersectionMatrix T hT Q' =
        NullCurveIntersectionMatrix.intersectionMatrix S hS Q := by
  classical
  obtain ⟨T, hT, b, hseq, hcontract, hpreserve, hintersection⟩ :=
    exists_contract_disjoint_family_intersections (GeneralResolution.contraction k)
      S hS E hminus hpair
  choose Q' hQ' using fun j => hpreserve (Q j) (havoid j)
  refine ⟨T, hT, b, Q', hseq, hcontract, hQ', ?_⟩
  funext i j
  change (T.intersectionPairing hT (T.primeCurveCartier hT (Q' i))
      (T.primeCurveCartier hT (Q' j)) : ℚ) =
    (S.intersectionPairing hS (S.primeCurveCartier hS (Q i))
      (S.primeCurveCartier hS (Q j)) : ℚ)
  rw [T.intersectionPairing_primeCurve hT, S.intersectionPairing_primeCurve hS]
  exact_mod_cast hintersection (Q j) (Q i) (havoid j) (havoid i)
    (Q' j) (Q' i) (hQ' j).1 (hQ' i).1

end KltDP.Geometry

#print axioms KltDP.Geometry.exists_blowdowns_with_surviving_family
