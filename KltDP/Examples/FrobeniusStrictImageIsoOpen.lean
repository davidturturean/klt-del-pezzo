import KltDP.Geometry.SchematicImageOpenBaseChange
import KltDP.Examples.FrobeniusTransversalContactsSPn

/-!
# The strict transforms over the isomorphism opens

Over the isomorphism open `V = isoPreimage q n a i` of `S_{p,n}`, on which the tower projection
`isoMap : V ⟶ T_i` is an open immersion, the lifted punctured graph of `S_{p,n}` and that of the tower
have the same preimage (`preimage_range_graphLift_eq`, from BRIEF6's `graphLift_towerProjection` and
`isoMap_preimage_lift_subset`), hence the same closure (`preimage_closure_graphLift_eq`). By the generic
`ker_openBaseChange_eq` the base changes of the two lifts to `V` therefore have the same kernel ideal
sheaf (`graphStrict_ker_isoOpen`) and literally the same glued image (`graphStrictIsoOpenImage`): over
the isomorphism open, the strict graph `B` and the tower closure `B_i` restrict to the same closed
subscheme of `V`. The same holds for the strict fibre `F_i` and the tower's strict fibre
(`fiberStrict_ker_isoOpen`, `fiberStrictIsoOpenImage`). Bundle `sPn_strict_image_isoOpen`.

Not done here: the identification of the base change of the *image* `B ×_S V` with the image of the
base change (glued-subscheme base change), which is what is still needed to move the contact lengths of
`sPn_transversal_contacts` onto the stalks of `B` and `F_i` themselves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictImageIsoOpen

open KltDP.Geometry KltDP.Geometry.SchematicImageOpenBaseChange FrobeniusGraphClosed
  FrobeniusStrictTransformClosure FrobeniusFiberClosure
  FrobeniusTranslatedCharts FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreGraphFiber FrobeniusAdaptedStrictTransform FrobeniusAdaptedFiberTransform
  FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreFiberContacts

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-! ## The strict fibre -/

/-- Over the isomorphism open, the lifted punctured fibres of `S_{p,n}` and of `T_i` have the same
preimage. -/
theorem preimage_range_fiberLift_eq (i : Fin n) :
    (isoPreimage q n a i).ι.base ⁻¹' Set.range (fiberLift (q + 1) n a i).base =
      (isoMap q n a i).base ⁻¹' Set.range ((towerFiber q n a i).lift (q + 1)).base := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz⟩
    rw [Scheme.Opens.ι_base_apply] at hz
    refine ⟨(fiberPunctureInclusion q n a i).base z, ?_⟩
    rw [isoMap_base, ← hz, ← Scheme.comp_base_apply, ← Scheme.comp_base_apply,
      fiberLift_towerProjection]
  · exact isoMap_preimage_fiberLift_subset q n a i

theorem preimage_closure_fiberLift_eq (i : Fin n) :
    (isoPreimage q n a i).ι.base ⁻¹' closure (Set.range (fiberLift (q + 1) n a i).base) =
      (isoMap q n a i).base ⁻¹' closure (Set.range ((towerFiber q n a i).lift (q + 1)).base) := by
  rw [(isoPreimage q n a i).ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    (isoPreimage q n a i).ι.isOpenEmbedding.continuous,
    (isoMap q n a i).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    (isoMap q n a i).isOpenEmbedding.continuous, preimage_range_fiberLift_eq]

/-- **Over the isomorphism open, `F_i` and the tower's strict fibre have the same ideal sheaf.** -/
theorem fiberStrict_ker_isoOpen (i : Fin n) :
    (openBaseChange (fiberLift (q + 1) n a i) (isoPreimage q n a i).ι).ker =
      (openBaseChange ((towerFiber q n a i).lift (q + 1)) (isoMap q n a i)).ker := by
  letI := fiberPuncture_noetherianSpace (q + 1) n a i
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : IsReduced (fiberPuncture (q + 1) n a i).toScheme :=
    isReduced_of_isOpenImmersion (fiberPuncture (q + 1) n a i).ι
  letI : IsReduced ((towerFiber q n a i).puncture).toScheme :=
    isReduced_of_isOpenImmersion ((towerFiber q n a i).puncture).ι
  exact ker_openBaseChange_eq _ _ _ _ (preimage_closure_fiberLift_eq q n a i)

/-- **The pulled-back strict fibre `F_i ×_S V` and the pulled-back tower strict fibre have the same
kernel on `V`** (both are the vanishing ideal of the preimage of the support). -/
theorem fiberStrictι_ker_isoOpen (i : Fin n) :
    (openBaseChange (fiberStrictι (q + 1) n a i) (isoPreimage q n a i).ι).ker =
      (openBaseChange (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))
        (isoMap q n a i)).ker := by
  letI := fiberPuncture_noetherianSpace (q + 1) n a i
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : IsReduced (fiberPuncture (q + 1) n a i).toScheme :=
    isReduced_of_isOpenImmersion (fiberPuncture (q + 1) n a i).ι
  letI : IsReduced (fiberStrict (q + 1) n a i) :=
    SchematicImageDenseOpen.image_glued_isReduced (fiberLift (q + 1) n a i)
  apply ker_openBaseChange_eq
  rw [range_fiberStrictι, closure_closure, range_fiberClosureInclusion_eq_closure_lift,
    closure_closure]
  exact preimage_closure_fiberLift_eq q n a i

/-- The restricted strict fibre is the restricted tower strict fibre, as glued images. -/
def fiberStrictIsoOpenImage (i : Fin n) :
    SchematicImageGlued.image (openBaseChange (fiberLift (q + 1) n a i) (isoPreimage q n a i).ι) ≅
      SchematicImageGlued.image
        (openBaseChange ((towerFiber q n a i).lift (q + 1)) (isoMap q n a i)) :=
  imageIsoOfKerEq _ _ (fiberStrict_ker_isoOpen q n a i)

/-! ## The strict graph -/

section Graph

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- Over the isomorphism open, the lifted punctured graphs of `S_{p,n}` and of `T_i` have the same
preimage. -/
theorem preimage_range_graphLift_eq (i : Fin n) :
    (isoPreimage q n a i).ι.base ⁻¹' Set.range (graphLift (q + 1) n a).base =
      (isoMap q n a i).base ⁻¹' Set.range ((towerGraph q n a i).lift (q + 1)).base := by
  apply Set.Subset.antisymm
  · rintro y ⟨z, hz⟩
    rw [Scheme.Opens.ι_base_apply] at hz
    refine ⟨(punctureInclusion q n a i).base z, ?_⟩
    rw [isoMap_base, ← hz, ← Scheme.comp_base_apply, ← Scheme.comp_base_apply,
      graphLift_towerProjection]
  · exact isoMap_preimage_lift_subset q n a i

theorem preimage_closure_graphLift_eq (i : Fin n) :
    (isoPreimage q n a i).ι.base ⁻¹' closure (Set.range (graphLift (q + 1) n a).base) =
      (isoMap q n a i).base ⁻¹' closure (Set.range ((towerGraph q n a i).lift (q + 1)).base) := by
  rw [(isoPreimage q n a i).ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    (isoPreimage q n a i).ι.isOpenEmbedding.continuous,
    (isoMap q n a i).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    (isoMap q n a i).isOpenEmbedding.continuous, preimage_range_graphLift_eq]

/-- **Over the isomorphism open, `B` and the tower closure have the same ideal sheaf.** -/
theorem graphStrict_ker_isoOpen (i : Fin n) :
    (openBaseChange (graphLift (q + 1) n a) (isoPreimage q n a i).ι).ker =
      (openBaseChange ((towerGraph q n a i).lift (q + 1)) (isoMap q n a i)).ker := by
  letI := graphPuncture_noetherianSpace (q + 1) n a
  letI : IsIntegral (graph (k := k) (q + 1)) := graph_isIntegral (q + 1)
  letI : IsReduced (graphPuncture (q + 1) n a).toScheme :=
    isReduced_of_isOpenImmersion (graphPuncture (q + 1) n a).ι
  letI : IsReduced ((towerGraph q n a i).puncture).toScheme :=
    isReduced_of_isOpenImmersion ((towerGraph q n a i).puncture).ι
  exact ker_openBaseChange_eq _ _ _ _ (preimage_closure_graphLift_eq q n a i)

/-- **The pulled-back strict graph `B ×_S V` and the pulled-back tower closure have the same kernel on
`V`.** -/
theorem graphStrictι_ker_isoOpen (i : Fin n) :
    (openBaseChange (graphStrictι (q + 1) n a) (isoPreimage q n a i).ι).ker =
      (openBaseChange (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0)
        (isoMap q n a i)).ker := by
  letI := graphPuncture_noetherianSpace (q + 1) n a
  letI : IsIntegral (graph (k := k) (q + 1)) := graph_isIntegral (q + 1)
  letI : IsReduced (graphPuncture (q + 1) n a).toScheme :=
    isReduced_of_isOpenImmersion (graphPuncture (q + 1) n a).ι
  letI : IsReduced (graphStrict (q + 1) n a) :=
    SchematicImageDenseOpen.image_glued_isReduced (graphLift (q + 1) n a)
  apply ker_openBaseChange_eq
  rw [range_graphStrictι, closure_closure, range_closureInclusion_eq_closure_lift, closure_closure]
  exact preimage_closure_graphLift_eq q n a i

/-- The restricted strict graph is the restricted tower closure, as glued images. -/
def graphStrictIsoOpenImage (i : Fin n) :
    SchematicImageGlued.image (openBaseChange (graphLift (q + 1) n a) (isoPreimage q n a i).ι) ≅
      SchematicImageGlued.image
        (openBaseChange ((towerGraph q n a i).lift (q + 1)) (isoMap q n a i)) :=
  imageIsoOfKerEq _ _ (graphStrict_ker_isoOpen q n a i)

end Graph

end KltDP.Examples.FrobeniusStrictImageIsoOpen

namespace KltDP.Examples

open KltDP.Geometry.SchematicImageOpenBaseChange FrobeniusStrictTransformClosure
  FrobeniusTranslatedCharts FrobeniusFiberClosure FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreFiberContacts FrobeniusStrictImageIsoOpen

/-- Bundle: over the isomorphism open of every tower, the strict graph and the strict fibre of
`S_{p,n}` have the same ideal sheaves as the tower closure and the tower strict fibre — for the base
changes of the defining lifts and for the base changes of the closed subschemes themselves. -/
theorem sPn_strict_image_isoOpen (k : Type u) [Field k] (q n : ℕ) [Fact (q + 1).Prime]
    [CharP k (q + 1)] (a : Fin n → k) :
    (∀ i : Fin n, (openBaseChange (graphLift (q + 1) n a) (isoPreimage q n a i).ι).ker =
      (openBaseChange ((towerGraph q n a i).lift (q + 1)) (isoMap q n a i)).ker) ∧
    (∀ i : Fin n, (openBaseChange (fiberLift (q + 1) n a i) (isoPreimage q n a i).ι).ker =
      (openBaseChange ((towerFiber q n a i).lift (q + 1)) (isoMap q n a i)).ker) ∧
    (∀ i : Fin n, (openBaseChange (graphStrictι (q + 1) n a) (isoPreimage q n a i).ι).ker =
      (openBaseChange (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0)
        (isoMap q n a i)).ker) ∧
    (∀ i : Fin n, (openBaseChange (fiberStrictι (q + 1) n a i) (isoPreimage q n a i).ι).ker =
      (openBaseChange (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))
        (isoMap q n a i)).ker) :=
  ⟨fun i => graphStrict_ker_isoOpen q n a i, fun i => fiberStrict_ker_isoOpen q n a i,
    fun i => graphStrictι_ker_isoOpen q n a i, fun i => fiberStrictι_ker_isoOpen q n a i⟩

/-- The bundle has exactly one universe parameter. -/
theorem sPn_strict_image_isoOpen_universe_check (k : Type u) [Field k] (q n : ℕ)
    [Fact (q + 1).Prime] [CharP k (q + 1)] (a : Fin n → k) : True := by
  have _ := sPn_strict_image_isoOpen.{u} k q n a
  trivial

end KltDP.Examples
