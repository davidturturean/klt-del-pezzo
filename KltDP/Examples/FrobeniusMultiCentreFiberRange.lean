import KltDP.Examples.FrobeniusMultiCentreFiberContacts
import KltDP.Examples.FrobeniusMultiCentreGraphNewest

/-!
# The strict fibre `F_i` and its tower model live in the isomorphism open

The fibre `y = a_i^p` of `P¹ ×_k P¹` passes through the selected centre `(a_i, a_i^p)` and through **no
other** selected centre: a centre `(a_j, a_j^p)` lies on it exactly when `a_j^p = a_i^p`, which in
characteristic `p` forces `a_j = a_i` (`frobenius_inj`), hence `j = i` for an injective selection
(`mem_otherComplement_of_mem_fiberRange`).  Consequently:

* the strict transform `F̃` of the fibre on the `i`-th tower has its whole support inside the open
  `isoOpen q n a i` over which `towerProjection` is an isomorphism
  (`range_fiberClosureInclusion_subset_isoOpen`): the support is the closure of the lifted punctured
  fibre (accepted `range_fiberClosureInclusion_eq_closure_lift`), the lift projects into the *closed*
  range of `horizontalFiberMorphism (a_i^p)` (accepted `FiberAdapted.lift_projection`, and the `ι` of
  `fiberAdaptedTranslated` is that very morphism), so the closure still projects into it;
* the strict transform `F_i ⊂ S_{p,n}` has its whole support inside the cluster open
  `isoPreimage q n a i` (`range_fiberStrictι_subset_isoPreimage`), directly from the accepted
  `fiberStrict_projection_mem`.

These are the two range statements that the global fibre row needs: with the first, the queued
`SchemeKernelBaseChangeIsoLocus.baseChangeKernelIso` applies to `g = fiberClosureInclusion …` and
`π = towerProjection …`; with the second, the ideal of `F_i` is the unit off `U_i`, which is the input
of the ideal-sheaf-data comparison (`IdealSheafData.ext_of_affine_cover`) that identifies `I(F_i)` with
the ideal of the base change.  Neither of those two steps is carried out here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreFiberRange

open FrobeniusProjectivePoints FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusGlobalBlowupStages FrobeniusAdaptedFiberTransform FrobeniusFiberClosure
  FrobeniusGraphPicardClassZeroFiber FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreFiberContacts

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

section Fibre

variable [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)] (ha : Function.Injective a)
  (i : Fin n)

include ha in
/-- **A point of the fibre `y = a_i^p` is never a centre other than the `i`-th one** (in
characteristic `p` the `p`-th power map is injective). -/
theorem mem_otherComplement_of_mem_fiberRange (x : projectiveProduct k)
    (hx : x ∈ Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base) :
    x ∈ otherComplement q n a i := by
  rw [mem_otherComplement_iff]
  intro j hj h
  obtain ⟨y, rfl⟩ := hx
  have h2 : point (a i ^ (q + 1)) = point (a j ^ (q + 1)) := by
    rw [← horizontalFiber_snd_base (a i ^ (q + 1)) y, h, graphPoint_snd]
  exact hj (ha (frobenius_inj k (q + 1)
    (show frobenius k (q + 1) (a j) = frobenius k (q + 1) (a i) from (point_injective h2).symm)))

include ha in
/-- **The support of `F_i ⊂ S_{p,n}` lies in the cluster open `U_i`.** -/
theorem range_fiberStrictι_subset_isoPreimage :
    Set.range (fiberStrictι (q + 1) n a i).base ⊆
      (isoPreimage q n a i : Set (multiSurface (q + 1) n a)) := by
  rintro _ ⟨x, rfl⟩
  show (selectedProjection (q + 1) (a i) (q + 1)).base
      ((towerProjection (q + 1) n a i).base ((fiberStrictι (q + 1) n a i).base x)) ∈
    otherComplement q n a i
  rw [← Scheme.comp_base_apply, towerProjection_projection]
  exact mem_otherComplement_of_mem_fiberRange q n a ha i _
    (fiberStrict_projection_mem (q + 1) n a i x)

include ha in
/-- **The support of the tower's strict fibre `F̃` lies in the isomorphism open `isoOpen`.** -/
theorem range_fiberClosureInclusion_subset_isoOpen :
    Set.range (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)).base ⊆
      (isoOpen q n a i : Set (selectedStage (q + 1) (a i) (q + 1))) := by
  rw [range_fiberClosureInclusion_eq_closure_lift]
  have hclosed : IsClosed ((selectedProjection (q + 1) (a i) (q + 1)).base ⁻¹'
      Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base) :=
    ((horizontalFiberMorphism (a i ^ (q + 1))).isClosedEmbedding.isClosed_range).preimage
      (selectedProjection (q + 1) (a i) (q + 1)).continuous
  have hsub : Set.range ((towerFiber q n a i).lift (q + 1)).base ⊆
      (selectedProjection (q + 1) (a i) (q + 1)).base ⁻¹'
        Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base := by
    rintro _ ⟨z, rfl⟩
    change ((towerFiber q n a i).lift (q + 1) ≫
      (translatedInitial (q + 1) (a i)).toInitial (q + 1)).base z ∈
        Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base
    rw [FiberAdapted.lift_projection]
    exact ⟨((towerFiber q n a i).puncture).ι.base z, rfl⟩
  intro y hy
  exact mem_otherComplement_of_mem_fiberRange q n a ha i _ (closure_minimal hsub hclosed hy)

end Fibre

end KltDP.Examples.FrobeniusMultiCentreFiberRange
