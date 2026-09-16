import KltDP.Geometry.SchematicImageToImageIso
import KltDP.Examples.FrobeniusStrictImageIsoOpen

/-!
# The strict transforms over the isomorphism opens, as schemes

Over the isomorphism open `V = isoPreimage q n a i`, the pulled-back strict graph `B ×_S V` and the
pulled-back tower closure `B_i ×_T isoOpen` are closed subschemes of `V` with reduced sources and, by
BRIEF13, the same kernel; by the generic `isoOfKerEq` they are isomorphic over `V`
(`graphRestrictIso`, `graphRestrictIso_hom_fst`). The same holds for the strict fibre
(`fiberRestrictIso`, `fiberRestrictIso_hom_fst`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictImageIso

open KltDP.Geometry KltDP.Geometry.SchematicImageOpenBaseChange
  KltDP.Geometry.SchematicImageToImageIso FrobeniusGraphClosed FrobeniusStrictTransformClosure
  FrobeniusFiberClosure FrobeniusTranslatedCharts FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber FrobeniusAdaptedStrictTransform
  FrobeniusAdaptedFiberTransform FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreFiberContacts FrobeniusStrictImageIsoOpen

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-! ## The strict fibre -/

/-- The pulled-back strict fibre `F_i ×_S V`. -/
abbrev fiberRestrict (i : Fin n) : Scheme.{u} :=
  pullback (isoPreimage q n a i).ι (fiberStrictι (q + 1) n a i)

/-- The pulled-back tower strict fibre `F̃_i ×_T isoOpen`. -/
abbrev towerFiberRestrict (i : Fin n) : Scheme.{u} :=
  pullback (isoMap q n a i) (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))

instance fiberRestrict_fst_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (pullback.fst (isoPreimage q n a i).ι (fiberStrictι (q + 1) n a i)) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

instance towerFiberRestrict_fst_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (pullback.fst (isoMap q n a i)
      (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1))) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

theorem fiberStrict_isReduced' (i : Fin n) : IsReduced (fiberStrict (q + 1) n a i) := by
  letI := fiberPuncture_noetherianSpace (q + 1) n a i
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : IsReduced (fiberPuncture (q + 1) n a i).toScheme :=
    isReduced_of_isOpenImmersion (fiberPuncture (q + 1) n a i).ι
  exact SchematicImageDenseOpen.image_glued_isReduced (fiberLift (q + 1) n a i)

instance fiberRestrict_isReduced (i : Fin n) : IsReduced (fiberRestrict q n a i) :=
  letI := fiberStrict_isReduced' q n a i
  isReduced_of_isOpenImmersion (pullback.snd (isoPreimage q n a i).ι (fiberStrictι (q + 1) n a i))

instance towerFiberRestrict_isReduced (i : Fin n) : IsReduced (towerFiberRestrict q n a i) :=
  isReduced_of_isOpenImmersion (pullback.snd (isoMap q n a i)
    (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)))

/-- **`F_i ×_S V ≅ F̃_i ×_T isoOpen`** over `V`. -/
def fiberRestrictIso (i : Fin n) : fiberRestrict q n a i ≅ towerFiberRestrict q n a i :=
  isoOfKerEq _ _ (fiberStrictι_ker_isoOpen q n a i)

@[reassoc] theorem fiberRestrictIso_hom_fst (i : Fin n) :
    (fiberRestrictIso q n a i).hom ≫
      pullback.fst (isoMap q n a i) (fiberClosureInclusion (translatedInitial (q + 1) (a i)) (q + 1)) =
        pullback.fst (isoPreimage q n a i).ι (fiberStrictι (q + 1) n a i) :=
  isoOfKerEq_hom _ _ _

/-! ## The strict graph -/

section Graph

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- The pulled-back strict graph `B ×_S V`. -/
abbrev graphRestrict (i : Fin n) : Scheme.{u} :=
  pullback (isoPreimage q n a i).ι (graphStrictι (q + 1) n a)

/-- The pulled-back tower closure `B_i ×_T isoOpen`. -/
abbrev towerGraphRestrict (i : Fin n) : Scheme.{u} :=
  pullback (isoMap q n a i) (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0)

instance graphRestrict_fst_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (pullback.fst (isoPreimage q n a i).ι (graphStrictι (q + 1) n a)) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

instance towerGraphRestrict_fst_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (pullback.fst (isoMap q n a i)
      (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0)) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

omit [Fact (q + 1).Prime] [CharP k (q + 1)] in
theorem graphStrict_isReduced' : IsReduced (graphStrict (q + 1) n a) := by
  letI := graphPuncture_noetherianSpace (q + 1) n a
  letI : IsIntegral (graph (k := k) (q + 1)) := graph_isIntegral (q + 1)
  letI : IsReduced (graphPuncture (q + 1) n a).toScheme :=
    isReduced_of_isOpenImmersion (graphPuncture (q + 1) n a).ι
  exact SchematicImageDenseOpen.image_glued_isReduced (graphLift (q + 1) n a)

instance graphRestrict_isReduced (i : Fin n) : IsReduced (graphRestrict q n a i) :=
  letI := graphStrict_isReduced' q n a
  isReduced_of_isOpenImmersion (pullback.snd (isoPreimage q n a i).ι (graphStrictι (q + 1) n a))

instance towerGraphRestrict_isReduced (i : Fin n) : IsReduced (towerGraphRestrict q n a i) :=
  isReduced_of_isOpenImmersion (pullback.snd (isoMap q n a i)
    (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0))

/-- **`B ×_S V ≅ B_i ×_T isoOpen`** over `V`. -/
def graphRestrictIso (i : Fin n) : graphRestrict q n a i ≅ towerGraphRestrict q n a i :=
  isoOfKerEq _ _ (graphStrictι_ker_isoOpen q n a i)

@[reassoc] theorem graphRestrictIso_hom_fst (i : Fin n) :
    (graphRestrictIso q n a i).hom ≫
      pullback.fst (isoMap q n a i) (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0) =
        pullback.fst (isoPreimage q n a i).ι (graphStrictι (q + 1) n a) :=
  isoOfKerEq_hom _ _ _

end Graph

end KltDP.Examples.FrobeniusStrictImageIso
