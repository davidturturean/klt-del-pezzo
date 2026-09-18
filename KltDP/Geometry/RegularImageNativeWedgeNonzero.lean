import KltDP.Geometry.BirationalNativeParameterWedgeNonzero
import KltDP.Geometry.RegularSurfacePointKaehlerParameters
import KltDP.Geometry.SmoothSurfaceRelativeDimension
import KltDP.Geometry.PrimeDivisor

/-!
# The same regular-image parameters have nonzero original pulled wedge

Use the vanishing parameters and primitive native basis produced by the
compiled regular-point theorem itself. The original birational stalk map
then pulls their exact differential wedge to a nonzero source-stalk wedge.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open IntrinsicNodal

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k) [hSmooth : IsSmooth S.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme) (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hbir : IsBirationalScheme π) (C : S.PrimeCurve)

include hSmooth hπ hbir in
/-- At a regular closed image of the original source prime, the same
vanishing parameters have primitive target wedge and nonzero pulled wedge. -/
theorem exists_regular_image_parameters_nonzero
    (hclosed : IsClosed ({π.base C.genericPoint} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme (π.base C.genericPoint)) :
    letI := stalkAlgebra X.structureMorphism (π.base C.genericPoint)
    letI := stalkAlgebra S.structureMorphism C.genericPoint
    ∃ (v : Fin 2 → maximalIdeal (X.stalk (π.base C.genericPoint)))
      (b : Basis (Fin 2) (X.stalk (π.base C.genericPoint))
        (KaehlerDifferential k (X.stalk (π.base C.genericPoint)))),
      (∀ i, b i = KaehlerDifferential.D k (X.stalk (π.base C.genericPoint)) (v i)) ∧
      Ideal.span (Set.range (fun i => (v i : X.stalk (π.base C.genericPoint)))) =
        maximalIdeal (X.stalk (π.base C.genericPoint)) ∧
      AffineTopDifferentialFrame.determinantEquiv b
        (exteriorPower.ιMulti (X.stalk (π.base C.genericPoint)) 2
          (fun i => KaehlerDifferential.D k (X.stalk (π.base C.genericPoint)) (v i))) = 1 ∧
      exteriorPower.ιMulti (S.stalk C.genericPoint) 2
        (fun i => KaehlerDifferential.D k (S.stalk C.genericPoint)
          (π.stalkMap C.genericPoint (v i))) ≠ 0 := by
  letI := stalkAlgebra X.structureMorphism (π.base C.genericPoint)
  letI := stalkAlgebra S.structureMorphism C.genericPoint
  letI := S.isSmoothOfRelativeDimension_two
  obtain ⟨v, b, hb, hspan, hprimitive⟩ :=
    X.exists_regular_closed_stalk_kaehler_parameters S.structureMorphism π hπ hbir
      (π.base C.genericPoint) hclosed hregular
  refine ⟨v, b, hb, hspan, hprimitive, ?_⟩
  exact BirationalNativeParameterWedgeNonzero.pulled_wedge_ne_zero
    S.structureMorphism X.structureMorphism π hπ hbir C.genericPoint
    (fun i => (v i : X.stalk (π.base C.genericPoint))) b hb

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
