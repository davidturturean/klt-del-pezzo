import KltDP.Examples.FrobeniusMultiCentreFiberIdeal

/-!
# From the ideal-sheaf-data equality to the isomorphism of ideal modules

`FrobeniusMultiCentreFiberIdeal` proves that `F_i` and the base change of the tower's strict fibre have
the same kernel as ideal-sheaf *data*.  Here that equality is turned into an isomorphism of the ideal
modules, by the accepted `isoOfKerEq` (two closed immersions with reduced sources and equal kernels have
isomorphic sources, compatibly with the immersions) followed by the accepted `schemeKernelPrecompIso`.

These three declarations elaborate large terms — the accepted `isoOfKerEq` unfolds the schematic-image
comparison — so they carry the permitted scoped `set_option maxHeartbeats 4000000` and are kept in this
separate module, away from the equality they rest on.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreFiberIdealIso

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
  KltDP.Geometry.SchematicImageOpenBaseChange KltDP.Geometry.SchematicImageToImageIso
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint FrobeniusFiberClosure
  FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreFiberRange FrobeniusMultiCentreFiberIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

section Fibre

variable [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)] (ha : Function.Injective a)
  (i : Fin n)

/-- The base change of a closed immersion is a closed immersion (the accepted idiom; this is not
found by instance search, and `local instance` does not cross module boundaries). -/
local instance baseChangeFst_isClosedImmersion :
    IsClosedImmersion (pullback.fst (towerProjection (q + 1) n a i)
      (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

set_option maxHeartbeats 4000000 in
/-- The two closed subschemes are isomorphic over `S_{p,n}`. -/
def fiberStrictIsoBaseChange :
    fiberStrict (q + 1) n a i ≅
      pullback (towerProjection (q + 1) n a i)
        (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)) :=
  letI := fiberStrict_isReduced (q + 1) n a i
  letI := baseChange_isReduced q n a ha i
  isoOfKerEq _ _ (fiberStrictι_ker_eq_baseChange_ker q n a ha i)

set_option maxHeartbeats 4000000 in
@[reassoc] theorem fiberStrictIsoBaseChange_hom :
    (fiberStrictIsoBaseChange q n a ha i).hom ≫
        pullback.fst (towerProjection (q + 1) n a i)
          (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)) =
      fiberStrictι (q + 1) n a i :=
  letI := fiberStrict_isReduced (q + 1) n a i
  letI := baseChange_isReduced q n a ha i
  isoOfKerEq_hom _ _ (fiberStrictι_ker_eq_baseChange_ker q n a ha i)

set_option maxHeartbeats 4000000 in
/-- **The ideal module of `F_i` is the ideal module of the base change.** -/
def fiberKernelGlobalIso :
    schemeKernelIdeal (fiberStrictι (q + 1) n a i) ≅
      schemeKernelIdeal (pullback.fst (towerProjection (q + 1) n a i)
        (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))) :=
  (schemeKernelIdealEqIso (fiberStrictIsoBaseChange_hom q n a ha i)).symm ≪≫
    schemeKernelPrecompIso (fiberStrictIsoBaseChange q n a ha i) _

end Fibre

end KltDP.Examples.FrobeniusMultiCentreFiberIdealIso
