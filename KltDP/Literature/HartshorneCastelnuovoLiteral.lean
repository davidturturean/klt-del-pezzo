import KltDP.Geometry.PointBlowupExceptionalFiberIso
import KltDP.Geometry.PointBlowupContraction
import KltDP.Literature.ResolutionLiterals

/-!
The complete Hartshorne Algebraic Geometry V.5.7 criterion, printed414.
The chapter's surface conventions are retained. The original exceptional
curve is identified with the actual point-blowup fiber as a scheme.
See the separate root admission decision and original-object dictionary.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry
universe u
namespace KltDP.Literature.Hartshorne
attribute [local instance] PointBlowupChart.instCommRing
  PointBlowupChart.instOpenImmersion PointBlowupChart.instMaximal

axiom castelnuovo_contraction_literal
    {k : Type u} [Field k] [IsAlgClosed k] :
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
              E.inclusion ≫ e.hom

end KltDP.Literature.Hartshorne
#check @KltDP.Literature.Hartshorne.castelnuovo_contraction_literal
#print axioms KltDP.Literature.Hartshorne.castelnuovo_contraction_literal
