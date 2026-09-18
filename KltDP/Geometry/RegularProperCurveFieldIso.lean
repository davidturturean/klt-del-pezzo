import KltDP.Geometry.RegularProperCurveGenericIso
import KltDP.Geometry.FunctionFieldAlgHomGenericTriangle

/-! The actual over-ground function-field equivalence of integral
regular proper curves extends to an actual over-ground scheme isomorphism.
The generic triangle retains the supplied field map, with its original
intrinsic stalk scalars. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RegularProperCurveFieldIso

open IntrinsicNodal

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    (hX : ∀ x : X, RegularPoint X x) (hY : ∀ y : Y, RegularPoint Y y)
    (dX : topologicalKrullDim X ≤ 1) (dY : topologicalKrullDim Y ≤ 1)
    (sX : X ⟶ Spec (CommRingCat.of k))
    (sY : Y ⟶ Spec (CommRingCat.of k)) [IsProper sX] [IsProper sY]

include hX hY dX dY in
theorem exists_iso :
    letI := stalkAlgebra sX (genericPoint X)
    letI := stalkAlgebra sY (genericPoint Y)
    ∀ e : Y.functionField ≃ₐ[k] X.functionField,
      ∃ i : X ≅ Y, i.hom ≫ sY = sX ∧
        X.fromSpecStalk (genericPoint X) ≫ i.hom =
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫
            Y.fromSpecStalk (genericPoint Y) := by
  letI := stalkAlgebra sX (genericPoint X)
  letI := stalkAlgebra sY (genericPoint Y)
  intro e
  exact RegularProperCurveGenericIso.exists_iso hX hY dX dY sX sY
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op)
    (FunctionFieldAlgHomGenericTriangle.triangle sX sY e.toAlgHom)

end KltDP.Geometry.RegularProperCurveFieldIso
