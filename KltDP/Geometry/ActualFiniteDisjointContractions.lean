import KltDP.Geometry.HartshorneFiniteDisjointContractions
import KltDP.Literature.HartshorneCastelnuovoLiteral

/-!
# Actual finite disjoint minus-one blowdowns

The separately reviewed full Castelnuovo theorem supplies only its
single-curve existence statement. The finite sequence and preservation
of every disjoint original curve are proved by the ordinary consumers.
The existing isolated Hartshorne dependency remains visible in the
printed axioms; no new literature statement is declared here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

/-- Contract an actual finite disjoint family, retaining all disjoint original curve schemes. -/
theorem exists_finite_disjoint_minusOne_blowdowns
    {k : Type u} [Field k] [IsAlgClosed k] {ι : Type*} [Finite ι]
    (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s) (C : ι → S.PrimeCurve)
    (hminus : ∀ i, IsMinusOneCurve hS (C i))
    (hpair : Pairwise (fun i j => Disjoint (C i : Set S.toScheme) (C j : Set S.toScheme))) :
    ∃ (T : NormalProjectiveSurface k)
      (hT : ∀ t : T.Point, RegularPoint T.toScheme t) (f : S.toScheme ⟶ T.toScheme),
      IsPointBlowupSequence S T f ∧ (∀ i, IsExceptionalCurve f (C i)) ∧
      ∀ D : S.PrimeCurve, (∀ i, Disjoint (D : Set S.toScheme) (C i : Set S.toScheme)) →
        ∃ D' : T.PrimeCurve, f.base '' (D : Set S.toScheme) = (D' : Set T.toScheme) ∧
          ∃ e : D'.toScheme ≅ D.toScheme,
            e.hom ≫ (D.inclusion ≫ f) = D'.inclusion ∧
            e.hom ≫ D.toSpec = D'.toSpec ∧
            D'.selfIntersectionNumber hT = D.selfIntersectionNumber hS :=
  exists_contract_disjoint_family_of_hartshorne
    KltDP.Literature.Hartshorne.castelnuovo_contraction_literal S hS C hminus hpair

end KltDP.Geometry

#check @KltDP.Geometry.exists_finite_disjoint_minusOne_blowdowns
#print axioms KltDP.Geometry.exists_finite_disjoint_minusOne_blowdowns
