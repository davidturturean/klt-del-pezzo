import KltDP.Geometry.GenericFiberStalkIso
import KltDP.Geometry.DominantGenericPoint
import KltDP.Geometry.BirationalAdapters

/-! If the literal generic-fiber structure morphism is an isomorphism,
the original dominant morphism is birational. The proof uses only the
original pullback square and its maps on the original stalks. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.GenericFiberIsomorphismBirational

theorem genericResidue_stalkMap_isIso (Y : Scheme.{u}) [IsIntegral Y]
    (z : Spec (Y.residueField (genericPoint Y))) :
    IsIso ((Y.fromSpecResidueField (genericPoint Y)).stalkMap z) := by
  letI := GenericFiberStalkIso.fromSpecResidueField_flat (Y := Y)
  let e := RingEquiv.ofBijective
    ((Y.fromSpecResidueField (genericPoint Y)).stalkMap z).hom
    (FlatSurjectiveLocalRingIso.bijective _
      (Flat.stalkMap (Y.fromSpecResidueField (genericPoint Y)) z)
      ((Y.fromSpecResidueField (genericPoint Y)).stalkMap_surjective z))
  exact e.toCommRingCatIso.isIso_hom

theorem isBirationalScheme {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    [IsIso (f.fiberToSpecResidueField (genericPoint Y))] : IsBirationalScheme f := by
  have hη : f.base (genericPoint X) = genericPoint Y :=
    (genericPointPreserving_of_isDominant f).base_genericPoint
  have hlift : genericPoint X ∈ Set.range (f.fiberι (genericPoint Y)).base := by
    rw [f.range_fiberι]
    exact hη
  obtain ⟨z, hz⟩ := hlift
  letI := GenericFiberStalkIso.stalkMap_isIso f z
  have hcomp : f.fiberι (genericPoint Y) ≫ f =
      f.fiberToSpecResidueField (genericPoint Y) ≫
        Y.fromSpecResidueField (genericPoint Y) := pullback.condition
  have hc : IsIso ((f.fiberι (genericPoint Y) ≫ f).stalkMap z) := by
    rw [hcomp, Scheme.stalkMap_comp]
    letI := genericResidue_stalkMap_isIso Y
      ((f.fiberToSpecResidueField (genericPoint Y)).base z)
    infer_instance
  letI : IsIso (f.stalkMap ((f.fiberι (genericPoint Y)).base z) ≫
      (f.fiberι (genericPoint Y)).stalkMap z) := by
    rw [← Scheme.stalkMap_comp]
    exact hc
  have hziso := IsIso.of_isIso_comp_right
    (f.stalkMap ((f.fiberι (genericPoint Y)).base z))
    ((f.fiberι (genericPoint Y)).stalkMap z)
  refine ⟨hη, ?_⟩
  exact Eq.mp (congrArg (fun x : X => IsIso (f.stalkMap x)) hz) hziso

#print axioms genericResidue_stalkMap_isIso
#print axioms isBirationalScheme

end KltDP.Geometry.GenericFiberIsomorphismBirational
