import KltDP.Examples.FrobeniusNonspecialRulingPrimeCurve

/-!
# The original infinity ruling fiber is unaffected and meets the strict graph

The original infinity section defines a closed horizontal projective line
in the original product. It avoids every finite center, so the accepted
isomorphism over the centers complement lifts the entire line. Pasting its
actual pullback square with the product fiber square identifies the literal
infinity ruling fiber with the original projective line. Prime-curve
maximality and the previously proved original graph point give the exclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusInfinityRulingPrimeCurve

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed
  FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreIntegral FrobeniusNonspecialRulingPrimeCurve
  FrobeniusRulingFiberMeetsGraph ProjectiveLinePointAtInfinity

variable {k : Type u} [Field k]

/-- The horizontal projective line at the original infinity section. -/
def horizontalInfinityMorphism : projectiveSpace k 1 ⟶ projectiveProduct k :=
  pullback.lift (𝟙 (projectiveSpace k 1))
    (projectiveSpaceToSpec k 1 ≫ infinityMorphism)
    (by rw [Category.id_comp, Category.assoc, infinityMorphism_over_base,
      Category.comp_id])

@[reassoc] theorem horizontalInfinityMorphism_fst :
    horizontalInfinityMorphism (k := k) ≫ firstProjection = 𝟙 (projectiveSpace k 1) :=
  pullback.lift_fst _ _ _

@[reassoc] theorem horizontalInfinityMorphism_snd :
    horizontalInfinityMorphism (k := k) ≫ secondProjection =
      projectiveSpaceToSpec k 1 ≫ infinityMorphism :=
  pullback.lift_snd _ _ _

instance horizontalInfinityMorphism_isClosedImmersion :
    IsClosedImmersion (horizontalInfinityMorphism (k := k)) := by
  haveI : IsClosedImmersion (horizontalInfinityMorphism (k := k) ≫ firstProjection) := by
    rw [horizontalInfinityMorphism_fst]
    infer_instance
  exact IsClosedImmersion.of_comp horizontalInfinityMorphism firstProjection

private theorem infinity_factor_structure {T : Scheme.{u}}
    (f : T ⟶ projectiveProduct k) (g : T ⟶ Spec (CommRingCat.of k))
    (w : f ≫ secondProjection = g ≫ infinityMorphism) :
    (f ≫ firstProjection) ≫ projectiveSpaceToSpec k 1 = g := by
  rw [Category.assoc, show firstProjection (k := k) ≫ projectiveSpaceToSpec k 1 =
    secondProjection ≫ projectiveSpaceToSpec k 1 from pullback.condition,
    ← Category.assoc, w, Category.assoc, infinityMorphism_over_base, Category.comp_id]

private theorem infinity_factor_embedding {T : Scheme.{u}}
    (f : T ⟶ projectiveProduct k) (g : T ⟶ Spec (CommRingCat.of k))
    (w : f ≫ secondProjection = g ≫ infinityMorphism) :
    (f ≫ firstProjection) ≫ horizontalInfinityMorphism = f := by
  apply pullback.hom_ext
  · rw [Category.assoc, horizontalInfinityMorphism_fst, Category.comp_id]
  · rw [Category.assoc, horizontalInfinityMorphism_snd, ← Category.assoc,
      infinity_factor_structure f g w]
    exact w.symm

/-- The horizontal infinity embedding is the literal product fiber square. -/
theorem horizontalInfinityMorphism_isPullback :
    IsPullback (horizontalInfinityMorphism (k := k)) (projectiveSpaceToSpec k 1)
      secondProjection infinityMorphism := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk horizontalInfinityMorphism_snd
    (fun s => s.fst ≫ firstProjection)
    (fun s => infinity_factor_embedding s.fst s.snd s.condition)
    (fun s => infinity_factor_structure s.fst s.snd s.condition) ?_)
  intro s m hm _
  have h := congrArg (fun f => f ≫ firstProjection (k := k)) hm
  simpa only [Category.assoc, horizontalInfinityMorphism_fst, Category.comp_id] using h

/-- Every point of that horizontal line has original second coordinate infinity. -/
theorem horizontalInfinityMorphism_snd_base (x : projectiveSpace k 1) :
    (secondProjection (k := k)).base (horizontalInfinityMorphism.base x) = infinityPoint := by
  change (horizontalInfinityMorphism ≫ secondProjection).base x = infinityPoint
  rw [horizontalInfinityMorphism_snd]
  change infinityMorphism.base ((projectiveSpaceToSpec k 1).base x) = infinityPoint
  rw [Subsingleton.elim ((projectiveSpaceToSpec k 1).base x) (IsLocalRing.closedPoint k)]
  exact fieldMorphismPoint_infinityMorphism

variable (q n : ℕ) (a : Fin n → k)

/-- The original infinity line avoids all of the original finite selected centers. -/
theorem horizontalInfinity_range_centersComplement :
    Set.range (horizontalInfinityMorphism (k := k)).base ⊆
      Set.range (centersComplement (q + 1) n a).ι.base := by
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨horizontalInfinityMorphism.base x, ?_⟩, rfl⟩
  rw [mem_centersComplement_iff]
  intro j hj
  have h := congrArg (secondProjection (k := k)).base hj
  rw [horizontalInfinityMorphism_snd_base, graphPoint_snd] at h
  exact infinityPoint_ne_point (a j ^ (q + 1)) h

/-- The original infinity line lifted through the accepted centers-complement isomorphism. -/
def infinityFiberLift : projectiveSpace k 1 ⟶ multiSurface (q + 1) n a :=
  letI := multiProjection_restrict_centersComplement_isIso (q + 1) n a
  liftOverIso (multiProjection (q + 1) n a) (centersComplement (q + 1) n a)
    horizontalInfinityMorphism (horizontalInfinity_range_centersComplement q n a)

/-- The complete preimage of the original infinity line is unaffected by the blowups. -/
theorem infinityFiberLift_isPullback :
    IsPullback (infinityFiberLift q n a) (𝟙 (projectiveSpace k 1))
      (multiProjection (q + 1) n a) horizontalInfinityMorphism := by
  letI := multiProjection_restrict_centersComplement_isIso (q + 1) n a
  exact liftOverIso_isPullback _ _ _ _

instance infinityFiberLift_isClosedImmersion : IsClosedImmersion (infinityFiberLift q n a) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (infinityFiberLift_isPullback q n a).flip inferInstance

/-- Pasting the two actual squares gives the original second-ruling infinity fiber square. -/
theorem infinityFiberLift_ruling_isPullback :
    IsPullback (infinityFiberLift q n a) (projectiveSpaceToSpec k 1)
      (multiProjection (q + 1) n a ≫ secondProjection) infinityMorphism := by
  simpa only [Category.id_comp] using
    (infinityFiberLift_isPullback q n a).paste_vert horizontalInfinityMorphism_isPullback

/-- The literal original infinity ruling fiber is isomorphic to the original projective line. -/
def infinityRulingFiberIso : projectiveSpace k 1 ≅
    pullback (multiProjection (q + 1) n a ≫ secondProjection) (infinityMorphism (k := k)) :=
  (infinityFiberLift_ruling_isPullback q n a).isoPullback

/-- The original lift has the entire original infinity ruling support. -/
theorem range_infinityFiberLift :
    Set.range (infinityFiberLift q n a).base =
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {infinityPoint} := by
  rw [range_eq_preimage_of_isPullback (infinityFiberLift_ruling_isPullback q n a),
    FrobeniusNonspecialRulingPrimeCurve.range_fieldMorphism, fieldMorphismPoint_infinityMorphism]

variable [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)]
variable (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Every original prime curve contained in the infinity ruling fiber meets the original strict graph. -/
theorem infinity_primeCurve_meets_graphStrict
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve)
    (hC : (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) ⊆
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {infinityPoint}) :
    ((C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) ∩
      Set.range (graphStrictι (q + 1) n a).base).Nonempty := by
  have heq := primeCurve_eq_range (multiSurfaceSurface (q + 1) n a ha hproj)
    (infinityFiberLift q n a) (Iso.refl _) C
    ((range_infinityFiberLift q n a).symm ▸ hC)
  have hsupport : (Set.range (infinityFiberLift q n a).base :
      Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) =
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {infinityPoint} :=
    range_infinityFiberLift (k := k) q n a
  let z : (multiSurfaceSurface (q + 1) n a ha hproj).toScheme :=
    (FrobeniusMultiCentreGraphProjectiveLine.globalGraphParametrization
      (q + 1) n a).base (infinityPoint (k := k))
  have hzheight : z ∈
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {infinityPoint} :=
    globalGraphParametrization_infinity_ruling q n a
  have hzlift : z ∈ Set.range (infinityFiberLift q n a).base :=
    (congrArg (fun T : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme =>
      z ∈ T) hsupport).mpr hzheight
  have hzC : z ∈ (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) :=
    (congrArg (fun T : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme =>
      z ∈ T) heq).mpr hzlift
  exact ⟨z, hzC, FrobeniusNonspecialRulingMeetsGraph.globalGraphParametrization_mem_graphStrict
    q n a (infinityPoint (k := k))⟩

/-- An original prime curve contained in the infinity ruling fiber cannot be graph-disjoint. -/
theorem infinity_primeCurve_not_disjoint_graphStrict
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve)
    (hC : (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) ⊆
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {infinityPoint})
    (hdisj : Disjoint (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme)
      (Set.range (graphStrictι (q + 1) n a).base)) : False := by
  obtain ⟨z, hzC, hzB⟩ := infinity_primeCurve_meets_graphStrict q n a ha hproj C hC
  exact Set.disjoint_left.mp hdisj hzC hzB

end KltDP.Examples.FrobeniusInfinityRulingPrimeCurve
