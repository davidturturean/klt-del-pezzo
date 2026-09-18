import KltDP.Geometry.BirationalFunctionFieldStalkAlgebra

/-! A homomorphism of the original function fields with the intrinsic
ground actions gives the literal over-ground generic spectrum triangle. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.FunctionFieldAlgHomGenericTriangle

open IntrinsicNodal

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ Spec (CommRingCat.of k))
    (sY : Y ⟶ Spec (CommRingCat.of k))

theorem triangle :
    letI := stalkAlgebra sX (genericPoint X)
    letI := stalkAlgebra sY (genericPoint Y)
    ∀ e : Y.functionField →ₐ[k] X.functionField,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y) ≫ sY =
          X.fromSpecStalk (genericPoint X) ≫ sX := by
  letI := stalkAlgebra sX (genericPoint X)
  letI := stalkAlgebra sY (genericPoint Y)
  intro e
  have h : baseToStalkMap sY (genericPoint Y) ≫
      CommRingCat.ofHom e.toRingHom = baseToStalkMap sX (genericPoint X) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact e.commutes a
  rw [← Spec_map_baseToStalkMap, ← Spec.map_comp, h, Spec_map_baseToStalkMap]

end KltDP.Geometry.FunctionFieldAlgHomGenericTriangle
