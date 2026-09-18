import KltDP.Geometry.FiniteDisjointMinusOneContractions
import KltDP.Geometry.HartshorneCastelnuovoContraction

/-!
# Finite disjoint contractions from the entire source criterion

The full Hartshorne V.5.7 hypothesis remains expanded and explicit,
including the original exceptional scheme and its actual inclusion map.
The finite-family constructor is an ordinary consumer of single-curve
existence; there is no new source predicate or literature declaration.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

attribute [local instance] PointBlowupChart.instCommRing
  PointBlowupChart.instOpenImmersion PointBlowupChart.instMaximal

/-- Successive actual blowdowns and preservation of all disjoint original
curves, from the complete single-curve Castelnuovo statement. -/
theorem exists_contract_disjoint_family_of_hartshorne
    {k : Type u} [Field k] [IsAlgClosed k]
    (hCastelnuovo :
      ∀ (S : NormalProjectiveSurface k)
        (hregular : ∀ s : S.Point, RegularPoint S.toScheme s) (E : S.PrimeCurve),
        (∃ eP : E.toScheme ≅ projectiveSpace k 1,
          eP.hom ≫ projectiveSpaceToSpec k 1 = E.toSpec) →
        E.selfIntersectionNumber hregular = -1 →
        ∃ (T : NormalProjectiveSurface k)
          (hT : ∀ t : T.Point, RegularPoint T.toScheme t)
          (b : S.toScheme ⟶ T.toScheme) (z : T.Point)
          (c : PointBlowupChart T.toScheme z) (e : S.toScheme ≅ c.scheme),
          b ≫ T.structureMorphism = S.structureMorphism ∧
          e.hom ≫ c.projection = b ∧
          ∃ θ : E.toScheme ≅ PointBlowupGluing.globalCenterFiber c.j c.q c.isClosed,
            θ.hom ≫ PointBlowupGluing.globalCenterFiberι c.j c.q c.isClosed =
              E.inclusion ≫ e.hom)
    {ι : Type*} [Finite ι] (S : NormalProjectiveSurface k)
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
  exists_contract_disjoint_family (castelnuovoContractionLiteral_of_hartshorne hCastelnuovo)
    S hS C hminus hpair

end KltDP.Geometry

#print axioms KltDP.Geometry.exists_contract_disjoint_family_of_hartshorne
