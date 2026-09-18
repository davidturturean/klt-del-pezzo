import KltDP.Geometry.NormalStalkDVR
import KltDP.Geometry.CodimensionOneOpen
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian
import KltDP.Geometry.DivisorOrder

/-!
# Actual divisorial stalks on normal finite-type models

Finite type over the original field derives local Noetherianity. Normality
and the actual codimension-one local dimension then give the original DVR
stalk, using the already proved normal-stalk theorem.
-/

noncomputable section
open AlgebraicGeometry
universe u

namespace KltDP.Geometry

attribute [local instance] integralSchemeStalk_isDomain

/-- No separate Noetherian or DVR hypothesis is needed on a normal
finite-type integral model's original codimension-one point. -/
theorem normalFiniteTypePoint_isDiscreteValuationRing
    {k : Type u} [Field k] {V : Scheme.{u}} [IsIntegral V]
    (σ : V ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ]
    (hnormal : IsNormalScheme V) (x : CodimensionOnePoint V) :
    IsDiscreteValuationRing (V.presheaf.stalk x.val) := by
  letI : IsLocallyNoetherian V := isLocallyNoetherian_of_locallyOfFiniteType_spec σ
  exact normalStalk_isDiscreteValuationRing_of_isLocallyNoetherian
    V hnormal x.val x.property

end KltDP.Geometry

#check @KltDP.Geometry.normalFiniteTypePoint_isDiscreteValuationRing
#print axioms KltDP.Geometry.normalFiniteTypePoint_isDiscreteValuationRing
