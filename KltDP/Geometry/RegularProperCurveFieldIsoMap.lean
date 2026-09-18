import KltDP.Geometry.RegularProperCurveFieldIso

/-! The extended original scheme isomorphism induces exactly the given
map of original function fields, not merely an abstract field equivalence. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RegularProperCurveFieldIso

open IntrinsicNodal

theorem functionFieldMap_eq_of_generic_triangle
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : X ⟶ Y) [GenericPointPreserving g]
    (e : Y.functionField ⟶ X.functionField)
    (he : X.fromSpecStalk (genericPoint X) ≫ g =
      Spec.map e ≫ Y.fromSpecStalk (genericPoint Y)) : functionFieldMap g = e := by
  apply Spec.map_injective
  apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
  exact (ProperBirationalCodimensionOne.functionFieldMap_fromSpecStalk g).trans he

theorem exists_iso_with_functionFieldMap
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (hX : ∀ x : X, RegularPoint X x) (hY : ∀ y : Y, RegularPoint Y y)
    (dX : topologicalKrullDim X ≤ 1) (dY : topologicalKrullDim Y ≤ 1)
    (sX : X ⟶ Spec (CommRingCat.of k))
    (sY : Y ⟶ Spec (CommRingCat.of k)) [IsProper sX] [IsProper sY] :
    letI := stalkAlgebra sX (genericPoint X)
    letI := stalkAlgebra sY (genericPoint Y)
    ∀ e : Y.functionField ≃ₐ[k] X.functionField,
      ∃ i : X ≅ Y, i.hom ≫ sY = sX ∧
        ∃ hi : GenericPointPreserving i.hom,
          @functionFieldMap X Y _ _ i.hom hi = CommRingCat.ofHom e.toRingHom := by
  letI := stalkAlgebra sX (genericPoint X)
  letI := stalkAlgebra sY (genericPoint Y)
  intro e
  obtain ⟨i, hs, hg⟩ := exists_iso hX hY dX dY sX sY e
  letI : GenericPointPreserving i.hom :=
    ⟨genericPoint_eq_of_isOpenImmersion i.hom⟩
  exact ⟨i, hs, inferInstance,
    functionFieldMap_eq_of_generic_triangle i.hom (CommRingCat.ofHom e.toRingHom) hg⟩

end KltDP.Geometry.RegularProperCurveFieldIso
