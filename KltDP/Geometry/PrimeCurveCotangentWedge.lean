import KltDP.RingTheory.DerivationCommonFactorWedge
import KltDP.Geometry.NormalStalkDVR
import KltDP.Geometry.RationalTreePicardIntrinsicNode

/-!
# Vanishing of the original cotangent wedge along a prime curve

For the actual generic point of a source prime curve, the existing normal
surface theorem supplies the DVR stalk. The original scheme stalk map sends
the target maximal ideal into that DVR's maximal ideal. The source Kähler
module uses the scalar map induced by its original structure morphism.

Thus every scalar evaluation of `d(π♯a) ∧ d(π♯b)` is a nonunit whenever
`a,b` vanish at the actual image point. In the contraction application these
will be parameters at a regular target closed point. No frame, discrepancy
coefficient identification, or singularity conclusion is claimed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PrimeCurveCotangentWedge

open KltDP.Examples.FrobeniusBlowupDifferential

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) (C : S.PrimeCurve)

local instance : Algebra k (S.stalk C.genericPoint) :=
  IntrinsicNodal.stalkAlgebra S.structureMorphism C.genericPoint

local instance : IsDiscreteValuationRing (S.stalk C.genericPoint) :=
  C.genericPoint_isDiscreteValuationRing

/-- This uses the literal original `π.stalkMap C.genericPoint`. -/
theorem coefficient_mem_maximalIdeal
    (a b : X.stalk (π.base C.genericPoint))
    (ha : a ∈ IsLocalRing.maximalIdeal (X.stalk (π.base C.genericPoint)))
    (hb : b ∈ IsLocalRing.maximalIdeal (X.stalk (π.base C.genericPoint)))
    (ell : (⋀[S.stalk C.genericPoint]^2
      (KaehlerDifferential k (S.stalk C.genericPoint))) →ₗ[S.stalk C.genericPoint]
        S.stalk C.genericPoint) :
    ell (wedgeTwo
      (KaehlerDifferential.D k (S.stalk C.genericPoint)
        ((π.stalkMap C.genericPoint).hom a))
      (KaehlerDifferential.D k (S.stalk C.genericPoint)
        ((π.stalkMap C.genericPoint).hom b))) ∈
      IsLocalRing.maximalIdeal (S.stalk C.genericPoint) := by
  exact KltDP.RingTheory.DerivationCommonFactorWedge.coefficient_mem_maximalIdeal
    (KaehlerDifferential.D k (S.stalk C.genericPoint)) ell _ _
    (map_nonunit (π.stalkMap C.genericPoint).hom a ha)
    (map_nonunit (π.stalkMap C.genericPoint).hom b hb)

/-- Any coordinate of this original wedge fails to be a local unit. -/
theorem coefficient_not_isUnit
    (a b : X.stalk (π.base C.genericPoint))
    (ha : a ∈ IsLocalRing.maximalIdeal (X.stalk (π.base C.genericPoint)))
    (hb : b ∈ IsLocalRing.maximalIdeal (X.stalk (π.base C.genericPoint)))
    (ell : (⋀[S.stalk C.genericPoint]^2
      (KaehlerDifferential k (S.stalk C.genericPoint))) →ₗ[S.stalk C.genericPoint]
        S.stalk C.genericPoint) :
    ¬ IsUnit (ell (wedgeTwo
      (KaehlerDifferential.D k (S.stalk C.genericPoint)
        ((π.stalkMap C.genericPoint).hom a))
      (KaehlerDifferential.D k (S.stalk C.genericPoint)
        ((π.stalkMap C.genericPoint).hom b)))) :=
  (IsLocalRing.mem_maximalIdeal _).mp
    (coefficient_mem_maximalIdeal π C a b ha hb ell)

end KltDP.Geometry.PrimeCurveCotangentWedge

#check @KltDP.Geometry.PrimeCurveCotangentWedge.coefficient_mem_maximalIdeal
#print axioms KltDP.Geometry.PrimeCurveCotangentWedge.coefficient_not_isUnit
