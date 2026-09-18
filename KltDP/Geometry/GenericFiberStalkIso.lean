import KltDP.Geometry.SchemeFromSpecStalkFlat
import KltDP.Geometry.FlatSurjectiveLocalRingIso
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Fiber

/-! The literal inclusion of the actual generic fiber induces isomorphisms
of the original local rings. Only the base is required to be integral. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.GenericFiberStalkIso

variable {X Y : Scheme.{u}} [IsIntegral Y]

theorem generic_residue_isIso : IsIso (Y.residue (genericPoint Y)) := by
  let e := RingEquiv.ofBijective (Y.residue (genericPoint Y)).hom
    ⟨(Y.residue (genericPoint Y)).hom.injective,
      Y.residue_surjective (genericPoint Y)⟩
  exact e.toCommRingCatIso.isIso_hom

theorem fromSpecResidueField_flat :
    Flat (Y.fromSpecResidueField (genericPoint Y)) := by
  letI := generic_residue_isIso (Y := Y)
  letI := SchemeFromSpecStalkFlat.fromSpecStalk_flat Y (genericPoint Y)
  unfold Scheme.fromSpecResidueField
  infer_instance

theorem fiberι_flat (f : X ⟶ Y) : Flat (f.fiberι (genericPoint Y)) := by
  letI := fromSpecResidueField_flat (Y := Y)
  change Flat (pullback.fst f (Y.fromSpecResidueField (genericPoint Y)))
  infer_instance

theorem stalkMap_isIso (f : X ⟶ Y) (x : f.fiber (genericPoint Y)) :
    IsIso ((f.fiberι (genericPoint Y)).stalkMap x) := by
  letI := fiberι_flat f
  let e := RingEquiv.ofBijective ((f.fiberι (genericPoint Y)).stalkMap x).hom
    (FlatSurjectiveLocalRingIso.bijective _
      (Flat.stalkMap (f.fiberι (genericPoint Y)) x)
      ((f.fiberι (genericPoint Y)).stalkMap_surjective x))
  exact e.toCommRingCatIso.isIso_hom

def stalkIso (f : X ⟶ Y) (x : f.fiber (genericPoint Y)) :
    X.presheaf.stalk ((f.fiberι (genericPoint Y)).base x) ≅
      (f.fiber (genericPoint Y)).presheaf.stalk x := by
  letI := stalkMap_isIso f x
  exact asIso ((f.fiberι (genericPoint Y)).stalkMap x)

theorem stalkIso_hom (f : X ⟶ Y) (x : f.fiber (genericPoint Y)) :
    (stalkIso f x).hom = (f.fiberι (genericPoint Y)).stalkMap x := rfl

#print axioms stalkMap_isIso

end KltDP.Geometry.GenericFiberStalkIso
