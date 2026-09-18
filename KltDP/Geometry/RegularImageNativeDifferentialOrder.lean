import KltDP.Geometry.RegularImageNativeWedgeNonzero
import KltDP.Geometry.SmoothSurfacePrimeStalkKaehlerFrame
import KltDP.Geometry.PrimeCurveCotangentWedge
import KltDP.Geometry.DivisorOrderPositiveLocalElement

/-!
# Positive order of the original differential at a regular contracted image

The same genuine target parameters give a nonzero original pulled wedge.
Their vanishing makes its coordinate in the actual source determinant
frame a nonunit. Its original DVR order is therefore strictly positive.
The identification with the canonical discrepancy is a separate theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open IntrinsicNodal

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S X : NormalProjectiveSurface k) [hSmooth : IsSmooth S.structureMorphism]
    (π : S.toScheme ⟶ X.toScheme) (C : S.PrimeCurve)

/-- The scalar of the literal original pulled differential wedge in the
native source frame constructed from the actual smooth surface. -/
def nativeParameterCoefficient
    (v : Fin 2 → X.stalk (π.base C.genericPoint)) : S.stalk C.genericPoint := by
  letI := stalkAlgebra S.structureMorphism C.genericPoint
  exact nativeKaehlerDeterminant S C
    (exteriorPower.ιMulti (S.stalk C.genericPoint) 2
      (fun i => KaehlerDifferential.D k (S.stalk C.genericPoint)
        ((π.stalkMap C.genericPoint).hom (v i))))

include hSmooth in
/-- Genuine native target parameters at the regular closed image have
strictly positive original differential order at this source prime. -/
theorem exists_regular_image_parameters_positive_order
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hbir : IsBirationalScheme π)
    (hclosed : IsClosed ({π.base C.genericPoint} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme (π.base C.genericPoint)) :
    letI := stalkAlgebra X.structureMorphism (π.base C.genericPoint)
    letI := C.genericPoint_isDiscreteValuationRing
    ∃ (v : Fin 2 → maximalIdeal (X.stalk (π.base C.genericPoint)))
      (b : Basis (Fin 2) (X.stalk (π.base C.genericPoint))
        (KaehlerDifferential k (X.stalk (π.base C.genericPoint)))),
      (∀ i, b i = KaehlerDifferential.D k (X.stalk (π.base C.genericPoint)) (v i)) ∧
      Ideal.span (Set.range (fun i => (v i : X.stalk (π.base C.genericPoint)))) =
        maximalIdeal (X.stalk (π.base C.genericPoint)) ∧
      AffineTopDifferentialFrame.determinantEquiv b
        (exteriorPower.ιMulti (X.stalk (π.base C.genericPoint)) 2
          (fun i => KaehlerDifferential.D k (X.stalk (π.base C.genericPoint)) (v i))) = 1 ∧
      let c := nativeParameterCoefficient S X π C (fun i => (v i : X.stalk (π.base C.genericPoint)))
      ∃ hc : c ≠ 0, 0 < stalkDivisorOrder S.toScheme C.genericPoint
        (RingTheory.fractionFieldUnit (S.stalk C.genericPoint) S.toScheme.functionField c hc) := by
  letI := stalkAlgebra X.structureMorphism (π.base C.genericPoint)
  letI := stalkAlgebra S.structureMorphism C.genericPoint
  letI := C.genericPoint_isDiscreteValuationRing
  obtain ⟨v, b, hb, hspan, hprimitive, hw⟩ :=
    exists_regular_image_parameters_nonzero S X π hπ hbir C hclosed hregular
  let w : Fin 2 → KaehlerDifferential k (S.stalk C.genericPoint) := fun i =>
    KaehlerDifferential.D k (S.stalk C.genericPoint) ((π.stalkMap C.genericPoint).hom (v i))
  let ell := nativeKaehlerDeterminant S C
  let c := nativeParameterCoefficient S X π C
    (fun i => (v i : X.stalk (π.base C.genericPoint)))
  have hc : c ≠ 0 := by
    intro hz
    apply hw
    apply ell.injective
    have hezero : ell (0 : ⋀[S.stalk C.genericPoint]^2
        (KaehlerDifferential k (S.stalk C.genericPoint))) = (0 : S.stalk C.genericPoint) :=
      ell.map_zero
    exact hz.trans hezero.symm
  have hcm : c ∈ maximalIdeal (S.stalk C.genericPoint) := by
    change ell (exteriorPower.ιMulti (S.stalk C.genericPoint) 2 w) ∈ _
    have heta : w = ![w 0, w 1] := by
      funext i
      fin_cases i <;> rfl
    rw [heta]
    exact PrimeCurveCotangentWedge.coefficient_mem_maximalIdeal π C
      (v 0) (v 1) (v 0).property (v 1).property ell.toLinearMap
  exact ⟨v, b, hb, hspan, hprimitive, hc,
    stalkDivisorOrder_algebraMap_pos_of_mem_maximalIdeal S.toScheme C.genericPoint c hc hcm⟩

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

#print axioms KltDP.Geometry.NormalProjectiveSurface.PrimeCurve.exists_regular_image_parameters_positive_order
