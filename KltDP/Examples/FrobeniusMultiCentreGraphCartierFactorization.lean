import KltDP.Examples.FrobeniusMultiCentreExceptionalLocalComparison
import KltDP.Examples.FrobeniusMultiCentreExceptionalVanishing
import KltDP.Examples.FrobeniusMultiCentreGraphCartierTotal
import KltDP.Examples.FrobeniusMultiCentreGraphCartierStrict
import KltDP.Geometry.CartierDivisorSupportedAtPoint

/-!
# The actual global weighted Cartier factorization of the Frobenius graph

The total graph divisor on the original multi-centre surface is the
original strict graph divisor plus the weighted original exceptional
divisors. On each original cluster open this is the proved translated
tower identity; the other clusters' exceptional factors vanish there.
On the common centre complement the total and strict kernels agree and
all exceptional factors vanish. The actual Cartier-sheaf cover glues
these equalities, including the empty set of selected centres.

The field is algebraically closed, the selected affine parameters are
injective, and `p = q + 1` is prime in characteristic `p`. Each selected
tower has depth `p`. No global graph identity, projectivity, numerical
intersection formula, or contraction is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphCartierFactorization

open KltDP.Geometry KltDP.Geometry.CartierDivisorPullbackComp
  KltDP.Geometry.CartierPullbackKernelTransport KltDP.Geometry.OpenImmersionRational
  KltDP.Geometry.CartierSupportedAtPoint KltDP.Geometry.SchematicImageOpenBaseChange
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
  FrobeniusGraphZeroCartier FrobeniusGraphPicardClassIntegral
  FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusStrictTransformClosure
  FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphNewest
  FrobeniusMultiCentreCurveKernels FrobeniusMultiCentreIntegral FrobeniusMultiCentreGenericPoint
  FrobeniusMultiCentreIsoOpenClasses FrobeniusStrictImageIsoOpen
  FrobeniusMultiCentreExceptionalCartier FrobeniusMultiCentreExceptionalVanishing
  FrobeniusMultiCentreExceptionalLocalComparison FrobeniusMultiCentreGraphCartierTotal
  FrobeniusMultiCentreGraphCartierStrict FrobeniusTranslatedGraphCartierIdentity
  FrobeniusTowerTransportCartier FrobeniusTowerFunctionField.PlaneChartedScheme

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance factorizationOpenGenericPointPreserving
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsOpenImmersion f] : GenericPointPreserving f :=
  FrobeniusMultiCentreExceptionalLocalComparison.openGenericPointPreserving f

/-- Restricting an actual Cartier pullback along an open immersion is
the pullback along the original composite morphism. -/
theorem restriction_pullback_comp {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z) [GenericPointPreserving g]
    (D : CartierDivisor Z) (hD : HasRegularCartierEquations Z D) :
    cartierRestrictionHom f (pullbackDivisor g D hD) = pullbackDivisor (f ≫ g) D hD :=
  (pullbackDivisor_eq_cartierRestriction f _ (pullbackDivisor_hasRegularEquations g D hD)).symm.trans
    (pullbackDivisor_comp f g D hD).symm

/-- Equality of the actual Cartier restrictions gives equality of the
ambient Cartier-sheaf sections on a nonempty open. No point or dimension data is needed. -/
theorem section_eq_of_cartierRestriction_eq {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (D E : CartierDivisor X)
    (h : cartierRestrictionHom U.ι D = cartierRestrictionHom U.ι E) :
    (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op E := by
  apply sub_eq_zero.mp
  have hz := map_eq_zero_of_cartierRestrictionHom_eq_zero (V := U) (D - E)
    (by rw [map_sub, h, sub_self])
  simpa only [map_sub] using hz

variable {k : Type u} [Field k]

local instance weightedProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance weightedInitialIntegral (p : ℕ) (b : k) :
    IsIntegral (translatedInitial p b).carrier := projectiveProduct_isIntegral

local instance selectedProjectionGenericPoint (p : ℕ) (b : k) (N : ℕ) :
    GenericPointPreserving (selectedProjection p b N) := by
  simpa only [selectedProjection, between_zero] using
    (translated_between_genericPointPreserving p b N)

/-- The original common complement is nonempty, also when there are no selected centres. -/
theorem commonComplement_nonempty [IsAlgClosed k] (q n : ℕ) (a : Fin n → k) :
    Nonempty (blowdownIsoOpen q n a) := by
  obtain ⟨x⟩ := earlierComplement_nonempty (q + 1) n a
  exact ⟨(blowdownIso q n a).inv.base x⟩

variable [IsAlgClosed k] (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

include ha

/-- The original exceptional factors contributed by one selected contact tower. -/
def multiWeightedExceptionalDivisor (i : Fin n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    CartierDivisor (multiSurface (q + 1) n a) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact (∑ j : Fin q, (j.val + 1) • multiExceptionalDivisor q n a ha i (.inl j)) +
    (q + 1) • multiExceptionalDivisor q n a ha i (.inr PUnit.unit)

/-- The actual weighted exceptional section vanishes on another cluster. -/
theorem weightedExceptional_restrict_foreign (i i' : Fin n) (hii' : i' ≠ i) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    (cartierDivisorSheaf (multiSurface (q + 1) n a)).val.map
      (homOfLE (le_top : isoPreimage q n a i ≤ ⊤)).op
      (multiWeightedExceptionalDivisor q n a ha i') = 0 := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  simp only [multiWeightedExceptionalDivisor, map_add, map_sum, map_nsmul]
  simp only [multiExceptionalDivisor_restrict_cluster q n a ha i i' hii',
    nsmul_zero, Finset.sum_const_zero, add_zero]

/-- Every actual weighted exceptional section vanishes on the common complement. -/
theorem weightedExceptional_restrict_complement (i : Fin n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    (cartierDivisorSheaf (multiSurface (q + 1) n a)).val.map
      (homOfLE (le_top : blowdownIsoOpen q n a ≤ ⊤)).op
      (multiWeightedExceptionalDivisor q n a ha i) = 0 := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  simp only [multiWeightedExceptionalDivisor, map_add, map_sum, map_nsmul]
  simp only [multiExceptionalDivisor_restrict_complement q n a ha i,
    nsmul_zero, Finset.sum_const_zero, add_zero]

variable [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- The actual global total graph restricts to the original translated total graph. -/
theorem totalGraph_restriction_cluster (i : Fin n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    cartierRestrictionHom (isoPreimage q n a i).ι (multiGraphTotalDivisor (q + 1) n a ha) =
      cartierRestrictionHom (isoMap q n a i)
        (translatedGraphTotalDivisor (q + 1) (a i) (q + 1)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  letI : GenericPointPreserving (multiProjection (q + 1) n a) :=
    multiProjection_genericPointPreserving (q + 1) n a ha
  have ht : pullbackDivisor (selectedProjection (q + 1) (a i) (q + 1))
      (graphZeroDivisor (q + 1)) (graphZeroDivisor_hasRegularEquations (q + 1)) =
      translatedGraphTotalDivisor (q + 1) (a i) (q + 1) := by
    simpa only [selectedProjection, between_zero] using
      (translatedGraphTotalDivisor_eq_intrinsic (q + 1) (a i) (q + 1)).symm
  calc
    _ = pullbackDivisor ((isoPreimage q n a i).ι ≫ multiProjection (q + 1) n a)
        (graphZeroDivisor (q + 1)) (graphZeroDivisor_hasRegularEquations (q + 1)) :=
      restriction_pullback_comp _ _ _ _
    _ = pullbackDivisor (isoMap q n a i ≫ selectedProjection (q + 1) (a i) (q + 1))
        (graphZeroDivisor (q + 1)) (graphZeroDivisor_hasRegularEquations (q + 1)) :=
      pullbackDivisor_congr_hom (ι_multiProjection q n a i) _ _
    _ = cartierRestrictionHom (isoMap q n a i)
        (pullbackDivisor (selectedProjection (q + 1) (a i) (q + 1))
          (graphZeroDivisor (q + 1)) (graphZeroDivisor_hasRegularEquations (q + 1))) :=
      (restriction_pullback_comp _ _ _ _).symm
    _ = _ := congrArg (cartierRestrictionHom (isoMap q n a i)) ht

/-- The actual global strict graph restricts to the translated strict graph,
by equality of the original embedded open-base-change kernels. -/
theorem strictGraph_restriction_cluster (i : Fin n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    cartierRestrictionHom (isoPreimage q n a i).ι (multiGraphStrictDivisor q n a ha) =
      cartierRestrictionHom (isoMap q n a i)
        (translatedGraphStrictDivisor (q + 1) (a i) (q + 1) 0) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  rw [← pullbackDivisor_eq_cartierRestriction _ _ (multiGraphStrictDivisor_hasRegularEquations q n a ha),
    ← pullbackDivisor_eq_cartierRestriction _ _
      (translatedGraphStrictDivisor_hasRegularEquations (q + 1) (a i) (q + 1) 0)]
  apply cartierDivisor_eq_of_idealData _ _ _
    (pullbackDivisor_hasRegularEquations _ _ _) (pullbackDivisor_hasRegularEquations _ _ _)
  change pullbackIdealData _ _ _ = pullbackIdealData _ _ _
  calc
    _ = (openBaseChange (graphStrictι (q + 1) n a) (isoPreimage q n a i).ι).ker :=
      pullbackIdealData_eq_kernel _ _ _ (graphStrictι (q + 1) n a) _ _
        (IsPullback.of_hasPullback _ _) (multiGraphStrictDivisor_idealData q n a ha)
    _ = (openBaseChange (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0)
        (isoMap q n a i)).ker := graphStrictι_ker_isoOpen q n a i
    _ = _ := (pullbackIdealData_eq_kernel _ _ _
      (closureInclusion (translatedInitial (q + 1) (a i)) (q + 1) 0) _ _
      (IsPullback.of_hasPullback _ _)
      (translatedGraphStrictDivisor_idealData (q + 1) (a i) (q + 1) 0)).symm

/-- The total graph on the common complement is the actual original graph divisor. -/
theorem totalGraph_restriction_complement :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : Nonempty (blowdownIsoOpen q n a) := commonComplement_nonempty q n a
    cartierRestrictionHom (blowdownIsoOpen q n a).ι (multiGraphTotalDivisor (q + 1) n a ha) =
      cartierRestrictionHom (blowdownMap q n a) (graphZeroDivisor (q + 1)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : Nonempty (blowdownIsoOpen q n a) := commonComplement_nonempty q n a
  letI : GenericPointPreserving (multiProjection (q + 1) n a) :=
    multiProjection_genericPointPreserving (q + 1) n a ha
  calc
    _ = pullbackDivisor ((blowdownIsoOpen q n a).ι ≫ multiProjection (q + 1) n a)
        (graphZeroDivisor (q + 1)) (graphZeroDivisor_hasRegularEquations (q + 1)) :=
      restriction_pullback_comp _ _ _ _
    _ = pullbackDivisor (blowdownMap q n a) (graphZeroDivisor (q + 1))
        (graphZeroDivisor_hasRegularEquations (q + 1)) :=
      pullbackDivisor_congr_hom (blowdownMap_eq q n a).symm _ _
    _ = _ := pullbackDivisor_eq_cartierRestriction _ _ _

/-- The strict graph has the same actual graph divisor on the common complement. -/
theorem strictGraph_restriction_complement :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : Nonempty (blowdownIsoOpen q n a) := commonComplement_nonempty q n a
    cartierRestrictionHom (blowdownIsoOpen q n a).ι (multiGraphStrictDivisor q n a ha) =
      cartierRestrictionHom (blowdownMap q n a) (graphZeroDivisor (q + 1)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : Nonempty (blowdownIsoOpen q n a) := commonComplement_nonempty q n a
  have hbase : effectiveCartierIdealDataOfRegularEquations _ (graphZeroDivisor (k := k) (q + 1))
      (graphZeroDivisor_hasRegularEquations (q + 1)) = (graphι (k := k) (q + 1)).ker := by
    rw [graphZeroDivisor_idealData, FrobeniusStrictTransformIsoProjectiveLine.graphι_eq_hom_comp,
      FrobeniusTowerTransportCurves.ker_comp_of_isIso]
    rfl
  rw [← pullbackDivisor_eq_cartierRestriction _ _ (multiGraphStrictDivisor_hasRegularEquations q n a ha),
    ← pullbackDivisor_eq_cartierRestriction _ _ (graphZeroDivisor_hasRegularEquations (q + 1))]
  apply cartierDivisor_eq_of_idealData _ _ _
    (pullbackDivisor_hasRegularEquations _ _ _) (pullbackDivisor_hasRegularEquations _ _ _)
  change pullbackIdealData _ _ _ = pullbackIdealData _ _ _
  calc
    _ = (openBaseChange (graphStrictι (q + 1) n a) (blowdownIsoOpen q n a).ι).ker :=
      pullbackIdealData_eq_kernel _ _ _ (graphStrictι (q + 1) n a) _ _
        (IsPullback.of_hasPullback _ _) (multiGraphStrictDivisor_idealData q n a ha)
    _ = (openBaseChange (graphι (k := k) (q + 1)) (blowdownMap q n a)).ker :=
      graphStrictι_ker_isoOpen₀ q n a
    _ = _ := (pullbackIdealData_eq_kernel _ _ _ (graphι (k := k) (q + 1)) _ _
      (IsPullback.of_hasPullback _ _) hbase).symm

/-- On a cluster, the actual total divisor equals the actual strict divisor
plus that cluster's weighted original exceptional divisors. -/
theorem weightedGraph_restriction_cluster (i : Fin n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
    cartierRestrictionHom (isoPreimage q n a i).ι (multiGraphTotalDivisor (q + 1) n a ha) =
      cartierRestrictionHom (isoPreimage q n a i).ι
        (multiGraphStrictDivisor q n a ha + multiWeightedExceptionalDivisor q n a ha i) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
  let towerIdentity (p : ℕ) : Prop :=
    translatedGraphTotalDivisor p (a i) (q + 1) =
      translatedGraphStrictDivisor p (a i) (q + 1) 0 +
        ∑ j : Fin q, (j.val + 1) • translatedOldFinalDivisor p (a i) (q + 1) j.val (by omega) +
        (q + 1) • translatedStepExceptionalDivisor p (a i) q
  have hraw : towerIdentity (0 + (q + 1)) := translatedGraphTotalDivisor_eq (k := k) q 0 (a i)
  have ht : towerIdentity (q + 1) :=
    Eq.mp (congrArg towerIdentity (Nat.zero_add (q + 1))) hraw
  have h := congrArg (cartierRestrictionHom (isoMap q n a i)) ht
  simp only [map_add, map_sum, map_nsmul] at h
  rw [totalGraph_restriction_cluster, map_add, strictGraph_restriction_cluster]
  simp only [multiWeightedExceptionalDivisor, map_add, map_sum, map_nsmul]
  simp only [global_restriction_eq_old, global_restriction_eq_newest,
    pullbackDivisor_eq_cartierRestriction]
  simpa only [add_assoc] using h

/-- The actual global Cartier factorization on the original multi-centre surface.
Each old component has coefficient `j + 1` and each newest component has coefficient `p = q + 1`. -/
theorem multiGraphTotalDivisor_eq_weighted :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    multiGraphTotalDivisor (q + 1) n a ha =
      multiGraphStrictDivisor q n a ha + ∑ i : Fin n, multiWeightedExceptionalDivisor q n a ha i := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  apply cartierDivisor_eq_of_restrict_eq _
    (fun t : ULift.{u} (Option (Fin n)) => match t.down with
      | none => blowdownIsoOpen q n a
      | some i => isoPreimage q n a i)
  · intro x _
    rcases cluster_cover q n a ha x with h | ⟨i, hi⟩
    · exact Opens.mem_iSup.mpr ⟨⟨none⟩, h⟩
    · exact Opens.mem_iSup.mpr ⟨⟨some i⟩, hi⟩
  · rintro ⟨t⟩
    cases t with
    | none =>
      letI : Nonempty (blowdownIsoOpen q n a) := commonComplement_nonempty q n a
      have h := section_eq_of_cartierRestriction_eq (blowdownIsoOpen q n a) _ _
        ((totalGraph_restriction_complement q n a ha).trans
          (strictGraph_restriction_complement q n a ha).symm)
      simpa only [map_add, map_sum, weightedExceptional_restrict_complement,
        Finset.sum_const_zero, add_zero] using h
    | some i =>
      letI : IsIntegral (isoPreimage q n a i).toScheme := ownCluster_isIntegral q n a ha i
      have h := section_eq_of_cartierRestriction_eq (isoPreimage q n a i) _ _
        (weightedGraph_restriction_cluster q n a ha i)
      rw [map_add] at h
      rw [map_add, map_sum, h]
      congr 1
      symm
      apply Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
      intro i' _ hii'
      exact weightedExceptional_restrict_foreign q n a ha i i' hii'

/-- The same actual global equality with the exceptional weights expanded. -/
theorem multiGraphTotalDivisor_eq_expanded :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    multiGraphTotalDivisor (q + 1) n a ha = multiGraphStrictDivisor q n a ha +
      ∑ i : Fin n, ((∑ j : Fin q, (j.val + 1) • multiExceptionalDivisor q n a ha i (.inl j)) +
        (q + 1) • multiExceptionalDivisor q n a ha i (.inr PUnit.unit)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  exact multiGraphTotalDivisor_eq_weighted q n a ha

end KltDP.Examples.FrobeniusMultiCentreGraphCartierFactorization
