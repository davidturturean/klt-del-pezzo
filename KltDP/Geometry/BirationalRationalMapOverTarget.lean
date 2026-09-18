import KltDP.Geometry.BirationalValuativeInverse
import Mathlib.AlgebraicGeometry.RationalMap

/-!
# The original rational map between birational models over their common target

Given original birational morphisms `t : T ⟶ X` and `v : V ⟶ X`, their original
function-field maps determine `K(V) ≅ K(T)` by inversion over `K(X)`. Its generic
map spreads to an actual partial map and rational map `T ⇢ V` over the original
`X` whenever `v` is locally of finite type (in particular, when `v` is proper).
The original generic map and both commutative triangles are proved here using
the pinned Mathlib spreading-out equivalence.

This constructs no domination, point-blowup factorization, or common resolution.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalRationalMapOverTarget

/-- The isomorphism is the original function-field map of the given morphism. -/
def functionFieldIso {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (f : Y ⟶ X) (hf : IsBirationalScheme f) : X.functionField ≅ Y.functionField := by
  letI : GenericPointPreserving f := ⟨hf.map_genericPoint⟩
  letI : IsIso (functionFieldMap f) :=
    (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso f).mp hf
  exact asIso (functionFieldMap f)

/-- The original function-field isomorphism has the original generic triangle. -/
theorem functionFieldIso_fromSpecStalk {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (f : Y ⟶ X) (hf : IsBirationalScheme f) :
    Spec.map (functionFieldIso f hf).hom ≫ X.fromSpecStalk (genericPoint X) =
      Y.fromSpecStalk (genericPoint Y) ≫ f := by
  letI : GenericPointPreserving f := ⟨hf.map_genericPoint⟩
  exact ProperBirationalCodimensionOne.functionFieldMap_fromSpecStalk f

variable {T V X : Scheme.{u}} [IsIntegral T] [IsIntegral V] [IsIntegral X]
  (t : T ⟶ X) (v : V ⟶ X) (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)

/-- The original contravariant field correspondence through the common target. -/
def fieldIso : V.functionField ≅ T.functionField :=
  (functionFieldIso v hv).symm ≪≫ functionFieldIso t ht

theorem fieldIso_hom :
    (fieldIso t v ht hv).hom = (functionFieldIso v hv).inv ≫ (functionFieldIso t ht).hom := rfl

/-- The field correspondence is over the original function field of `X`. -/
theorem functionFieldIso_fieldIso_hom :
    (functionFieldIso v hv).hom ≫ (fieldIso t v ht hv).hom = (functionFieldIso t ht).hom := by
  rw [fieldIso_hom, Iso.hom_inv_id_assoc]

/-- The generic map is induced by the original field correspondence. -/
def genericMap : Spec T.functionField ⟶ V :=
  Spec.map (fieldIso t v ht hv).hom ≫ V.fromSpecStalk (genericPoint V)

/-- The original generic correspondence commutes with the original maps to `X`. -/
theorem genericMap_comp :
    genericMap t v ht hv ≫ v = T.fromSpecStalk (genericPoint T) ≫ t := by
  dsimp only [genericMap]
  rw [Category.assoc, ← functionFieldIso_fromSpecStalk v hv, ← Category.assoc,
    ← Spec.map_comp, functionFieldIso_fieldIso_hom, functionFieldIso_fromSpecStalk t ht]

variable [LocallyOfFiniteType v]

/-- A dense-open representative obtained by spreading the original generic map. -/
def partialMap : T.PartialMap V :=
  Scheme.PartialMap.ofFromSpecStalk t v (genericMap t v ht hv) (genericMap_comp t v ht hv)

/-- The dense-open representative commutes with the original morphisms to `X`. -/
theorem partialMap_comp :
    (partialMap t v ht hv).hom ≫ v = (partialMap t v ht hv).domain.ι ≫ t :=
  Scheme.PartialMap.ofFromSpecStalk_comp t v (genericMap t v ht hv) (genericMap_comp t v ht hv)

theorem genericPoint_mem_partialMap_domain :
    genericPoint T ∈ (partialMap t v ht hv).domain :=
  Scheme.PartialMap.mem_domain_ofFromSpecStalk t v (genericMap t v ht hv)
    (genericMap_comp t v ht hv)

/-- Spreading out preserves the specified original generic map. -/
theorem partialMap_fromFunctionField :
    (partialMap t v ht hv).fromFunctionField = genericMap t v ht hv :=
  Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk t v (genericMap t v ht hv)
    (genericMap_comp t v ht hv)

/-- The rational map between the original models over the original target. -/
def rationalMap : T.RationalMap V :=
  Scheme.RationalMap.ofFunctionField t v (genericMap t v ht hv) (genericMap_comp t v ht hv)

theorem partialMap_toRationalMap :
    (partialMap t v ht hv).toRationalMap = rationalMap t v ht hv := rfl

theorem rationalMap_fromFunctionField :
    (rationalMap t v ht hv).fromFunctionField = genericMap t v ht hv :=
  Scheme.RationalMap.fromFunctionField_ofFunctionField t v (genericMap t v ht hv)
    (genericMap_comp t v ht hv)

/-- The rational map is over `X`; compatibility is produced by the pinned equivalence. -/
theorem rationalMap_compHom :
    (rationalMap t v ht hv).compHom v = t.toRationalMap :=
  ((Scheme.RationalMap.equivFunctionField t v)
    ⟨genericMap t v ht hv, genericMap_comp t v ht hv⟩).property

/-- The `IsOver` predicate uses the two original morphisms as structure maps. -/
theorem rationalMap_isOver :
    letI : T.Over X := ⟨t⟩
    letI : V.Over X := ⟨v⟩
    (rationalMap t v ht hv).IsOver X := by
  letI : T.Over X := ⟨t⟩
  letI : V.Over X := ⟨v⟩
  exact Scheme.RationalMap.isOver_iff.mpr (rationalMap_compHom t v ht hv)

include ht hv in
/-- The construction supplies an actual dense open and an original map over `X`. -/
theorem exists_denseOpen_map :
    ∃ (U : T.Opens) (_ : Dense (U : Set T)) (f : U.toScheme ⟶ V),
      f ≫ v = U.ι ≫ t :=
  ⟨(partialMap t v ht hv).domain, (partialMap t v ht hv).dense_domain,
    (partialMap t v ht hv).hom, partialMap_comp t v ht hv⟩

end KltDP.Geometry.BirationalRationalMapOverTarget
