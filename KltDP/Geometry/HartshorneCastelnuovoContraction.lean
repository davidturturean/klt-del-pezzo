import KltDP.Geometry.PointBlowupExceptionalFiberIso
import KltDP.Geometry.PointBlowupContraction
import KltDP.Literature.ResolutionLiterals

/-!
# Ordinary consumer of the complete Hartshorne V.5.7 criterion

The expanded hypothesis retains the original P1 isomorphism over k,
original self-intersection, target nonsingular projective surface, original
point-blowup isomorphism, and original exceptional-scheme identification.
The actual fiber, center dimension, and birationality are derived by the
ordinary point-blowup adapters. No literature declaration is activated here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

attribute [local instance] PointBlowupChart.instCommRing
  PointBlowupChart.instOpenImmersion PointBlowupChart.instMaximal

/-- The full source criterion implies the existing constructor interface,
with the same original surface, curve, target, center, and morphism. -/
theorem castelnuovoContractionLiteral_of_hartshorne
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
              E.inclusion ≫ e.hom) :
    KltDP.Literature.Stacks.CastelnuovoContractionLiteral k := by
  constructor
  intro S hregular E hE
  obtain ⟨T, hT, b, z, c, e, hover, he, θ, hθ⟩ :=
    hCastelnuovo S hregular E hE.isoProjectiveLine hE.selfIntersection
  have hbl : IsPointBlowupAt S T b z := ⟨hover, c, e, he⟩
  exact ⟨T, b, hbl.isContraction_of_exceptionalFiber hT E
    (c.pointFiber_eq_of_exceptionalIso e he E θ hθ)⟩

end KltDP.Geometry

#print axioms KltDP.Geometry.castelnuovoContractionLiteral_of_hartshorne
