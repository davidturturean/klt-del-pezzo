import KltDP.Geometry.BirationalFunctionField
import KltDP.Geometry.RationalTreePicardIntrinsicNode

/-!
# The original birational function-field map over the original base

The existing functionFieldMap is the original generic stalk map composed
with its canonical generic-point specialization. Its scalar compatibility
is obtained from the same original scheme maps by full faithfulness of
Spec. Birationality makes this actual algebra map an equivalence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalFunctionFieldStalkAlgebra

open IntrinsicNodal

variable {k : Type u} [CommRing k] {S X : Scheme.{u}}
    [IsIntegral S] [IsIntegral X]
    (f : S ⟶ Spec (CommRingCat.of k)) (σ : X ⟶ Spec (CommRingCat.of k))
    (π : S ⟶ X) (hπ : π ≫ σ = f)

section Map

variable [GenericPointPreserving π]

include hπ in
/-- The literal original function-field map preserves the original stalk scalars. -/
theorem scalar_triangle :
    baseToStalkMap σ (genericPoint X) ≫ functionFieldMap π =
      baseToStalkMap f (genericPoint S) := by
  rw [← hπ]
  apply Spec.map_injective
  simp only [functionFieldMap, Spec.map_comp, Spec_map_baseToStalkMap,
    Category.assoc, Scheme.Spec_map_stalkSpecializes_fromSpecStalk_assoc,
    Scheme.Spec_map_stalkMap_fromSpecStalk_assoc]

include hπ in
/-- The original field map, with the two intrinsic ground algebra structures. -/
def hom :
    letI := stalkAlgebra σ (genericPoint X)
    letI := stalkAlgebra f (genericPoint S)
    X.functionField →ₐ[k] S.functionField := by
  letI := stalkAlgebra σ (genericPoint X)
  letI := stalkAlgebra f (genericPoint S)
  refine { (functionFieldMap π).hom with commutes' := ?_ }
  intro r
  exact congrArg (fun g : CommRingCat.of k ⟶ S.functionField => g.hom r)
    (scalar_triangle f σ π hπ)

/-- No replacement field homomorphism was chosen. -/
theorem hom_toRingHom :
    letI := stalkAlgebra σ (genericPoint X)
    letI := stalkAlgebra f (genericPoint S)
    (hom f σ π hπ).toRingHom = (functionFieldMap π).hom := rfl

end Map

include hπ in
/-- Birationality supplies an algebra equivalence for this exact field map. -/
def equiv (hbir : IsBirationalScheme π) :
    letI := stalkAlgebra σ (genericPoint X)
    letI := stalkAlgebra f (genericPoint S)
    X.functionField ≃ₐ[k] S.functionField := by
  letI := stalkAlgebra σ (genericPoint X)
  letI := stalkAlgebra f (genericPoint S)
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsIso (functionFieldMap π) :=
    (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso π).mp hbir
  exact AlgEquiv.ofBijective (hom f σ π hπ)
    (ConcreteCategory.bijective_of_isIso (functionFieldMap π))

/-- The equivalence has the original function-field map as its forward map. -/
theorem equiv_toRingHom (hbir : IsBirationalScheme π) :
    letI := stalkAlgebra σ (genericPoint X)
    letI := stalkAlgebra f (genericPoint S)
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    (equiv f σ π hπ hbir).toRingHom = (functionFieldMap π).hom := rfl

end KltDP.Geometry.BirationalFunctionFieldStalkAlgebra
