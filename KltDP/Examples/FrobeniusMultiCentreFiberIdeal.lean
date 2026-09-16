import KltDP.Examples.FrobeniusMultiCentreFiberRange
import KltDP.Examples.FrobeniusStrictImageIsoOpen
import KltDP.Geometry.SchematicImageToImageIso
import KltDP.Geometry.SchemePullbackOverOpenIso
import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-!
# `F_i` is the base change of the tower's strict fibre

The strict transform `F_i ⊂ S_{p,n}` is a *schematic image*, not a pullback, so — unlike the
exceptional curves — it is not definitionally the base change of the corresponding tower curve.  This
module proves that it nevertheless **is** that base change, as a closed subscheme:

* `range_baseChange_eq_range_fiberStrictι`: `range (pullback.fst π_i F̃) = range F_i`.  One inclusion is
  the accepted `fiberStrict_projection_mem_towerStrict`; the other uses the compiled
  `range_fiberClosureInclusion_subset_isoOpen` (so every point over `F̃` lies in the cluster open) and
  then the accepted `preimage_closure_fiberLift_eq`, which compares the two closures over that open.
* `fiberStrictι_ker_eq_baseChange_ker`: the two kernels agree, by the accepted
  `ker_eq_of_closure_range_eq` (both sources are reduced: `F_i` by `fiberStrict_isReduced`, the base
  change because `pullback.snd π_i F̃` is an isomorphism, by the accepted
  `isIso_pullback_snd_of_range_subset` fed with the same compiled range statement).
The isomorphism of ideal *modules* built from this equality lives in the separate module
`FrobeniusMultiCentreFiberIdealIso`: that construction elaborates heavy terms and is kept apart so a
heartbeat timeout there cannot cost this equality.

This is the ideal-sheaf-data step: the equality is of *data*, so no gluing of modules is involved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreFiberIdeal

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
  KltDP.Geometry.SchematicImageOpenBaseChange KltDP.Geometry.SchematicImageToImageIso
open FrobeniusProjectivePoints FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusAdaptedFiberTransform FrobeniusFiberClosure FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreFiberContacts FrobeniusStrictImageIsoOpen FrobeniusMultiCentreFiberRange

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

section Fibre

variable [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)] (ha : Function.Injective a)
  (i : Fin n)

/-- The base change of the tower's strict fibre is a closed immersion (the accepted idiom; this is
not found by instance search). -/
local instance baseChangeFst_isClosedImmersion :
    IsClosedImmersion (pullback.fst (towerProjection (q + 1) n a i)
      (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

include ha in
/-- The tower's strict fibre lies in the range of the isomorphism open, in the form the accepted
`isIso_pullback_snd_of_range_subset` wants. -/
theorem range_fiberClosure_subset_range_ι :
    Set.range (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base ⊆
      Set.range (isoOpen q n a i).ι.base := by
  rw [Scheme.Opens.range_ι]
  exact range_fiberClosureInclusion_subset_isoOpen q n a ha i

include ha in
/-- **The base change of the tower's strict fibre has the same support as `F_i`.** -/
theorem range_baseChange_eq_range_fiberStrictι :
    Set.range (pullback.fst (towerProjection (q + 1) n a i)
        (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))).base =
      Set.range (fiberStrictι (q + 1) n a i).base := by
  rw [Scheme.Pullback.range_fst]
  apply Set.Subset.antisymm
  · intro x hx
    have hmem : x ∈ isoPreimage q n a i :=
      range_fiberClosureInclusion_subset_isoOpen q n a ha i hx
    have hy : (⟨x, hmem⟩ : (isoPreimage q n a i).toScheme) ∈
        (isoMap q n a i).base ⁻¹' closure (Set.range ((towerFiber q n a i).lift (q + 1)).base) := by
      show (isoMap q n a i).base ⟨x, hmem⟩ ∈
        closure (Set.range ((towerFiber q n a i).lift (q + 1)).base)
      rw [isoMap_base, ← range_fiberClosureInclusion_eq_closure_lift]
      exact hx
    rw [← preimage_closure_fiberLift_eq q n a i] at hy
    rw [range_fiberStrictι]
    exact hy
  · rintro _ ⟨x, rfl⟩
    exact fiberStrict_projection_mem_towerStrict q n a i _ ⟨x, rfl⟩

include ha in
/-- The base change of the tower's strict fibre along the tower projection is an isomorphism onto it. -/
theorem isIso_baseChange_snd :
    IsIso (pullback.snd (towerProjection (q + 1) n a i)
      (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))) :=
  isIso_pullback_snd_of_range_subset (towerProjection (q + 1) n a i)
    (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)) (isoOpen q n a i)
    (range_fiberClosure_subset_range_ι q n a ha i)

include ha in
/-- Hence its source is reduced. -/
theorem baseChange_isReduced :
    IsReduced (pullback (towerProjection (q + 1) n a i)
      (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))) := by
  letI := isIso_baseChange_snd q n a ha i
  exact isReduced_of_isOpenImmersion (pullback.snd (towerProjection (q + 1) n a i)
    (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)))

include ha in
/-- **`F_i` and the base change of the tower's strict fibre have the same ideal sheaf data.** -/
theorem fiberStrictι_ker_eq_baseChange_ker :
    (fiberStrictι (q + 1) n a i).ker =
      (pullback.fst (towerProjection (q + 1) n a i)
        (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))).ker := by
  letI := fiberStrict_isReduced (q + 1) n a i
  letI := baseChange_isReduced q n a ha i
  exact ker_eq_of_closure_range_eq _ _
    (congrArg closure (range_baseChange_eq_range_fiberStrictι q n a ha i).symm)

end Fibre

end KltDP.Examples.FrobeniusMultiCentreFiberIdeal
