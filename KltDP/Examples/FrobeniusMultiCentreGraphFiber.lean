import KltDP.Geometry.SchemeLiftOverIsoOpen
import KltDP.Examples.FrobeniusMultiCentreExceptional
import KltDP.Examples.FrobeniusGraphRationalPoints

/-!
# The strict transforms `B` and `F_i` of the graph and the tangent fibres in `S_{p,n}`

On the multi-centre surface `S_{p,n} = multiSurface p n a` (lane F), the projection `Π` to
`X = P¹ ×_k P¹` is an isomorphism over the complement `V` of the `n` selected centres
(`multiProjection_restrict_isIso`). The whole graph `graphι p` minus the centres lifts uniquely to
`S_{p,n}` (`liftOverIso`), and its schematic image (the accepted quotient-glued kernel subscheme,
`SchematicImageGlued.image`) is the strict transform `B` of the graph. Likewise the fibre
`y = (a i)^p` (accepted `horizontalFiberMorphism`) minus the centres lifts, and its schematic image is
the strict transform `F_i` of the `i`-th tangent fibre.

Proved here for every field, with `[IsAlgClosed k]` for distinct points and `[Fact p.Prime]
[CharP k p]` where Frobenius injectivity is needed:

* `B` and every `F_i` are closed subschemes of `S_{p,n}` (closed immersions `graphStrictι`,
  `fiberStrictι`), reduced and integral (the punctured graph and punctured fibre are integral,
  Noetherian opens of the projective line; the accepted reduced-image and irreducible-closure
  arguments apply);
* the punctured graph and punctured fibre factor through `B`, `F_i`, and the lifts are literal
  pullbacks of the punctured curves along `Π`;
* every point of `B` projects into the graph, every point of `F_i` projects into the fibre
  `y = (a i)^p`; distinct fibres `F_i`, `F_j` are disjoint, and `F_i` is disjoint from every
  exceptional curve of a tower `j ≠ i`.

Not proved (honest assessment in `F29_GRAPH_FIBERS.md`): the contacts `B ∩ P_i ≠ ∅`,
`B ∩ C_{ij} = ∅`, `F_i ∩ P_i ≠ ∅`, `F_i ∩ C_{ij} = ∅`, `B ∩ F_i = ∅`, single-point intersections,
and `B ≅ P¹`, `F_i ≅ P¹`. These need the whole-graph/strict-fibre contact analysis on the translated
towers, which the accepted library provides only for the origin tower.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphFiber

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
  FrobeniusGraphRationalPoints FrobeniusGraphPicardClassZeroFiber
  FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreSurface
  FrobeniusMultiCentreExceptional

variable {k : Type u} [Field k]

section Setup

variable (p n : ℕ) (a : Fin n → k)

/-- The complement of all selected centres in the projective product. -/
abbrev centersComplement : (projectiveProduct k).Opens := earlierComplement p n a

theorem mem_centersComplement_iff (x : projectiveProduct k) :
    x ∈ centersComplement p n a ↔ ∀ i, x ≠ graphPoint p (a i) :=
  mem_earlierComplement_iff p n a x

theorem multiProjection_restrict_centersComplement_isIso :
    IsIso (multiProjection p n a ∣_ centersComplement p n a) :=
  multiProjection_restrict_isIso p n a _ (not_mem_earlierComplement p n a)

end Setup

/-! ## The strict transform of the graph -/

section Graph

variable (p n : ℕ) (a : Fin n → k)

/-- The whole closed graph minus the selected centres. -/
def graphPuncture : (graph (k := k) p).Opens := graphι p ⁻¹ᵁ centersComplement p n a

/-- The punctured graph, as a morphism to the projective product. -/
def puncturedGraph : (graphPuncture p n a).toScheme ⟶ projectiveProduct k :=
  (graphPuncture p n a).ι ≫ graphι p

theorem puncturedGraph_range :
    Set.range (puncturedGraph p n a).base ⊆ Set.range (centersComplement p n a).ι.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨(puncturedGraph p n a).base z, z.2⟩, rfl⟩

/-- The lift of the punctured graph to the multi-centre surface. -/
def graphLift : (graphPuncture p n a).toScheme ⟶ multiSurface p n a :=
  letI := multiProjection_restrict_centersComplement_isIso p n a
  liftOverIso (multiProjection p n a) (centersComplement p n a) (puncturedGraph p n a)
    (puncturedGraph_range p n a)

@[reassoc] theorem graphLift_projection :
    graphLift p n a ≫ multiProjection p n a = puncturedGraph p n a := by
  letI := multiProjection_restrict_centersComplement_isIso p n a
  exact liftOverIso_comp _ _ _ _

theorem graphLift_isPullback :
    IsPullback (graphLift p n a) (𝟙 _) (multiProjection p n a) (puncturedGraph p n a) := by
  letI := multiProjection_restrict_centersComplement_isIso p n a
  exact liftOverIso_isPullback _ _ _ _

/-- The strict transform `B` of the graph: the schematic image of the lifted punctured graph. -/
abbrev graphStrict : Scheme.{u} := SchematicImageGlued.image (graphLift p n a)

/-- Its closed immersion into `S_{p,n}`. -/
abbrev graphStrictι : graphStrict p n a ⟶ multiSurface p n a :=
  SchematicImageGlued.inclusion (graphLift p n a)

instance graphStrictι_isClosedImmersion : IsClosedImmersion (graphStrictι p n a) :=
  SchematicImageGlued.inclusion_isClosedImmersion _

/-- The punctured graph factors through `B`. -/
def puncturedGraphToStrict : (graphPuncture p n a).toScheme ⟶ graphStrict p n a :=
  SchematicImageGlued.toImage (graphLift p n a)

@[reassoc] theorem puncturedGraphToStrict_ι :
    puncturedGraphToStrict p n a ≫ graphStrictι p n a = graphLift p n a :=
  SchematicImageGlued.toImage_inclusion _

/-- The punctured graph is an integral Noetherian open of the projective line. -/
theorem graphPuncture_noetherianSpace :
    TopologicalSpace.NoetherianSpace (graphPuncture p n a).toScheme := by
  letI := projectiveSpace_noetherianSpace k 1
  exact ((graphPuncture p n a).ι ≫
    (graphIsoProjectiveLine (k := k) p).hom).isOpenEmbedding.isInducing.noetherianSpace

/-- The support of `B` is the closure of the lifted punctured graph. -/
theorem range_graphStrictι :
    Set.range (graphStrictι p n a).base = closure (Set.range (graphLift p n a).base) := by
  letI := graphPuncture_noetherianSpace p n a
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact Scheme.Hom.support_ker (graphLift p n a)

/-- Every point of `B` projects into the graph. -/
theorem graphStrict_projection_mem (x : graphStrict p n a) :
    (multiProjection p n a).base ((graphStrictι p n a).base x) ∈
      Set.range (graphι (k := k) p).base := by
  have hx : (graphStrictι p n a).base x ∈ closure (Set.range (graphLift p n a).base) := by
    rw [← range_graphStrictι]
    exact ⟨x, rfl⟩
  have hsub : (multiProjection p n a).base '' closure (Set.range (graphLift p n a).base) ⊆
      closure ((multiProjection p n a).base '' Set.range (graphLift p n a).base) :=
    image_closure_subset_closure_image (multiProjection p n a).continuous
  have him : (multiProjection p n a).base '' Set.range (graphLift p n a).base ⊆
      Set.range (graphι (k := k) p).base := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(graphPuncture p n a).ι.base z, ?_⟩
    change (puncturedGraph p n a).base z = (graphLift p n a ≫ multiProjection p n a).base z
    rw [graphLift_projection]
  have hcl : closure ((multiProjection p n a).base '' Set.range (graphLift p n a).base) ⊆
      Set.range (graphι (k := k) p).base :=
    closure_minimal him (graphι (k := k) p).isClosedEmbedding.isClosed_range
  exact hcl (hsub ⟨_, hx, rfl⟩)

variable [IsAlgClosed k]

/-- A rational graph point avoiding all the selected centres. -/
theorem exists_graphPoint_not_center : ∃ c : k, ∀ i, graphPoint p c ≠ graphPoint p (a i) := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset (Finset.univ.image a)
  refine ⟨c, fun i h => hc ?_⟩
  rw [Finset.mem_image]
  exact ⟨i, Finset.mem_univ i, (graphPoint_injective p h).symm⟩

theorem graphPuncture_nonempty : Nonempty (graphPuncture p n a).toScheme := by
  obtain ⟨c, hc⟩ := exists_graphPoint_not_center p n a
  refine ⟨⟨graphRationalPoint p c, ?_⟩⟩
  change (graphι p).base (graphRationalPoint p c) ∈ centersComplement p n a
  rw [graphRationalPoint_ι, mem_centersComplement_iff]
  exact hc

theorem graphPuncture_isIntegral : IsIntegral (graphPuncture p n a).toScheme := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : Nonempty (graph (k := k) p) :=
    ⟨(graphIsoProjectiveLine (k := k) p).inv.base (Classical.choice inferInstance)⟩
  letI : IsIntegral (graph (k := k) p) :=
    isIntegral_of_isOpenImmersion (graphIsoProjectiveLine (k := k) p).hom
  letI := graphPuncture_nonempty p n a
  exact isIntegral_of_isOpenImmersion (graphPuncture p n a).ι

/-- `B` is reduced. -/
theorem graphStrict_isReduced : IsReduced (graphStrict p n a) := by
  letI := graphPuncture_isIntegral p n a
  letI := graphPuncture_noetherianSpace p n a
  exact SchematicImageDenseOpen.image_glued_isReduced (graphLift p n a)

theorem graphStrict_support_isIrreducible :
    IsIrreducible (((graphLift p n a).ker).support : Set (multiSurface p n a)) := by
  letI := graphPuncture_isIntegral p n a
  letI := graphPuncture_noetherianSpace p n a
  rw [Scheme.Hom.support_ker]
  have h := (IrreducibleSpace.isIrreducible_univ (graphPuncture p n a).toScheme).image
    (graphLift p n a).base (graphLift p n a).continuous.continuousOn
  simpa only [Set.image_univ] using h.closure

theorem graphStrict_irreducibleSpace : IrreducibleSpace (graphStrict p n a) := by
  let I := (graphLift p n a).ker
  letI : IrreducibleSpace I.support :=
    Subtype.irreducibleSpace (graphStrict_support_isIrreducible p n a)
  apply (irreducibleSpace_def (graphStrict p n a)).mpr
  have h := (IrreducibleSpace.isIrreducible_univ I.support).image
    I.gluedSupportHomeomorph.symm I.gluedSupportHomeomorph.symm.continuous.continuousOn
  simpa only [Set.image_univ, I.gluedSupportHomeomorph.symm.surjective.range_eq] using h

/-- `B` is an integral curve. -/
theorem graphStrict_isIntegral : IsIntegral (graphStrict p n a) := by
  letI := graphStrict_isReduced p n a
  letI := graphStrict_irreducibleSpace p n a
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Graph

/-! ## The strict transforms of the tangent fibres -/

section Fibers

variable (p n : ℕ) (a : Fin n → k)

/-- The fibre `y = (a i)^p` minus the selected centres, as an open of the projective line. -/
def fiberPuncture (i : Fin n) : (projectiveSpace k 1).Opens :=
  horizontalFiberMorphism (a i ^ p) ⁻¹ᵁ centersComplement p n a

/-- The punctured fibre, as a morphism to the projective product. -/
def puncturedFiber (i : Fin n) : (fiberPuncture p n a i).toScheme ⟶ projectiveProduct k :=
  (fiberPuncture p n a i).ι ≫ horizontalFiberMorphism (a i ^ p)

theorem puncturedFiber_range (i : Fin n) :
    Set.range (puncturedFiber p n a i).base ⊆ Set.range (centersComplement p n a).ι.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨(puncturedFiber p n a i).base z, z.2⟩, rfl⟩

/-- The lift of the punctured fibre to the multi-centre surface. -/
def fiberLift (i : Fin n) : (fiberPuncture p n a i).toScheme ⟶ multiSurface p n a :=
  letI := multiProjection_restrict_centersComplement_isIso p n a
  liftOverIso (multiProjection p n a) (centersComplement p n a) (puncturedFiber p n a i)
    (puncturedFiber_range p n a i)

@[reassoc] theorem fiberLift_projection (i : Fin n) :
    fiberLift p n a i ≫ multiProjection p n a = puncturedFiber p n a i := by
  letI := multiProjection_restrict_centersComplement_isIso p n a
  exact liftOverIso_comp _ _ _ _

theorem fiberLift_isPullback (i : Fin n) :
    IsPullback (fiberLift p n a i) (𝟙 _) (multiProjection p n a) (puncturedFiber p n a i) := by
  letI := multiProjection_restrict_centersComplement_isIso p n a
  exact liftOverIso_isPullback _ _ _ _

/-- The strict transform `F_i` of the tangent fibre `y = (a i)^p`. -/
abbrev fiberStrict (i : Fin n) : Scheme.{u} := SchematicImageGlued.image (fiberLift p n a i)

/-- Its closed immersion into `S_{p,n}`. -/
abbrev fiberStrictι (i : Fin n) : fiberStrict p n a i ⟶ multiSurface p n a :=
  SchematicImageGlued.inclusion (fiberLift p n a i)

instance fiberStrictι_isClosedImmersion (i : Fin n) : IsClosedImmersion (fiberStrictι p n a i) :=
  SchematicImageGlued.inclusion_isClosedImmersion _

/-- The punctured fibre factors through `F_i`. -/
def puncturedFiberToStrict (i : Fin n) : (fiberPuncture p n a i).toScheme ⟶ fiberStrict p n a i :=
  SchematicImageGlued.toImage (fiberLift p n a i)

@[reassoc] theorem puncturedFiberToStrict_ι (i : Fin n) :
    puncturedFiberToStrict p n a i ≫ fiberStrictι p n a i = fiberLift p n a i :=
  SchematicImageGlued.toImage_inclusion _

theorem fiberPuncture_noetherianSpace (i : Fin n) :
    TopologicalSpace.NoetherianSpace (fiberPuncture p n a i).toScheme := by
  letI := projectiveSpace_noetherianSpace k 1
  exact (fiberPuncture p n a i).ι.isOpenEmbedding.isInducing.noetherianSpace

/-- The second coordinate of every point of the fibre `y = c` is the rational point `[1:c]`. -/
theorem horizontalFiber_snd_base (c : k) (y : projectiveSpace k 1) :
    (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
      ((horizontalFiberMorphism c).base y) = point c := by
  change (horizontalFiberMorphism c ≫ secondProjection).base y = point c
  rw [horizontalFiberMorphism_snd]
  change (pointMorphism c).base ((projectiveSpaceToSpec k 1).base y) = point c
  rw [Subsingleton.elim ((projectiveSpaceToSpec k 1).base y) (IsLocalRing.closedPoint k)]
  rfl

theorem horizontalFiber_fst_base (c : k) (y : projectiveSpace k 1) :
    (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base
      ((horizontalFiberMorphism c).base y) = y := by
  change (horizontalFiberMorphism c ≫ firstProjection).base y = y
  rw [horizontalFiberMorphism_fst]
  rfl

/-- The support of `F_i` is the closure of the lifted punctured fibre. -/
theorem range_fiberStrictι (i : Fin n) :
    Set.range (fiberStrictι p n a i).base = closure (Set.range (fiberLift p n a i).base) := by
  letI := fiberPuncture_noetherianSpace p n a i
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact Scheme.Hom.support_ker (fiberLift p n a i)

/-- Every point of `F_i` projects into the fibre `y = (a i)^p`. -/
theorem fiberStrict_projection_mem (i : Fin n) (x : fiberStrict p n a i) :
    (multiProjection p n a).base ((fiberStrictι p n a i).base x) ∈
      Set.range (horizontalFiberMorphism (a i ^ p)).base := by
  have hx : (fiberStrictι p n a i).base x ∈ closure (Set.range (fiberLift p n a i).base) := by
    rw [← range_fiberStrictι]
    exact ⟨x, rfl⟩
  have hsub : (multiProjection p n a).base '' closure (Set.range (fiberLift p n a i).base) ⊆
      closure ((multiProjection p n a).base '' Set.range (fiberLift p n a i).base) :=
    image_closure_subset_closure_image (multiProjection p n a).continuous
  have him : (multiProjection p n a).base '' Set.range (fiberLift p n a i).base ⊆
      Set.range (horizontalFiberMorphism (a i ^ p)).base := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(fiberPuncture p n a i).ι.base z, ?_⟩
    change (puncturedFiber p n a i).base z = (fiberLift p n a i ≫ multiProjection p n a).base z
    rw [fiberLift_projection]
  have hcl : closure ((multiProjection p n a).base '' Set.range (fiberLift p n a i).base) ⊆
      Set.range (horizontalFiberMorphism (a i ^ p)).base :=
    closure_minimal him (horizontalFiberMorphism (a i ^ p)).isClosedEmbedding.isClosed_range
  exact hcl (hsub ⟨_, hx, rfl⟩)

variable [IsAlgClosed k]

/-- Points of two fibre strict transforms with distinct second coordinates are distinct. -/
theorem fiberStrict_disjoint_of_pow_ne {i j : Fin n} (hij : a i ^ p ≠ a j ^ p) :
    Disjoint (Set.range (fiberStrictι p n a i).base) (Set.range (fiberStrictι p n a j).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨x', hx'⟩
  obtain ⟨y, hy⟩ := fiberStrict_projection_mem p n a i x
  have h2 := fiberStrict_projection_mem p n a j x'
  rw [hx'] at h2
  obtain ⟨y', hy'⟩ := h2
  apply hij
  apply point_injective
  rw [← horizontalFiber_snd_base (a i ^ p) y, hy, ← hy', horizontalFiber_snd_base]

/-- A rational point of the fibre `y = (a i)^p` avoiding all selected centres. -/
theorem exists_fiberPoint_not_center (i : Fin n) :
    ∃ c : k, ∀ j, (horizontalFiberMorphism (a i ^ p)).base (point c) ≠ graphPoint p (a j) := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset (Finset.univ.image a)
  refine ⟨c, fun j h => hc ?_⟩
  rw [Finset.mem_image]
  refine ⟨j, Finset.mem_univ j, ?_⟩
  have h1 := congrArg (pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base h
  rw [horizontalFiber_fst_base, graphPoint_fst] at h1
  exact (point_injective h1).symm

theorem fiberPuncture_nonempty (i : Fin n) : Nonempty (fiberPuncture p n a i).toScheme := by
  obtain ⟨c, hc⟩ := exists_fiberPoint_not_center p n a i
  refine ⟨⟨point c, ?_⟩⟩
  change (horizontalFiberMorphism (a i ^ p)).base (point c) ∈ centersComplement p n a
  rw [mem_centersComplement_iff]
  exact hc

theorem fiberPuncture_isIntegral (i : Fin n) : IsIntegral (fiberPuncture p n a i).toScheme := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI := fiberPuncture_nonempty p n a i
  exact isIntegral_of_isOpenImmersion (fiberPuncture p n a i).ι

/-- `F_i` is reduced. -/
theorem fiberStrict_isReduced (i : Fin n) : IsReduced (fiberStrict p n a i) := by
  letI := fiberPuncture_isIntegral p n a i
  letI := fiberPuncture_noetherianSpace p n a i
  exact SchematicImageDenseOpen.image_glued_isReduced (fiberLift p n a i)

theorem fiberStrict_support_isIrreducible (i : Fin n) :
    IsIrreducible (((fiberLift p n a i).ker).support : Set (multiSurface p n a)) := by
  letI := fiberPuncture_isIntegral p n a i
  letI := fiberPuncture_noetherianSpace p n a i
  rw [Scheme.Hom.support_ker]
  have h := (IrreducibleSpace.isIrreducible_univ (fiberPuncture p n a i).toScheme).image
    (fiberLift p n a i).base (fiberLift p n a i).continuous.continuousOn
  simpa only [Set.image_univ] using h.closure

theorem fiberStrict_irreducibleSpace (i : Fin n) : IrreducibleSpace (fiberStrict p n a i) := by
  let I := (fiberLift p n a i).ker
  letI : IrreducibleSpace I.support :=
    Subtype.irreducibleSpace (fiberStrict_support_isIrreducible p n a i)
  apply (irreducibleSpace_def (fiberStrict p n a i)).mpr
  have h := (IrreducibleSpace.isIrreducible_univ I.support).image
    I.gluedSupportHomeomorph.symm I.gluedSupportHomeomorph.symm.continuous.continuousOn
  simpa only [Set.image_univ, I.gluedSupportHomeomorph.symm.surjective.range_eq] using h

/-- `F_i` is an integral curve. -/
theorem fiberStrict_isIntegral (i : Fin n) : IsIntegral (fiberStrict p n a i) := by
  letI := fiberStrict_isReduced p n a i
  letI := fiberStrict_irreducibleSpace p n a i
  exact isIntegral_of_irreducibleSpace_of_isReduced _


variable [Fact p.Prime] [CharP k p] (ha : Function.Injective a)
include ha

/-- Distinct tangent fibres have disjoint strict transforms. -/
theorem fiberStrict_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Set.range (fiberStrictι p n a i).base) (Set.range (fiberStrictι p n a j).base) :=
  fiberStrict_disjoint_of_pow_ne p n a (fun h => hij (ha (frobenius_inj k p h)))

end Fibers

/-! ## Fibres against the exceptional curves of the other towers -/

section Exceptional

variable (q n : ℕ) (a : Fin n → k) [IsAlgClosed k] [Fact (q + 1).Prime] [CharP k (q + 1)]
  (ha : Function.Injective a)
include ha

/-- `F_i` is disjoint from every exceptional curve of a tower `j ≠ i`: the exceptional curves of
tower `j` lie over `(a j, (a j)^p)`, whose second coordinate differs from `(a i)^p`. -/
theorem fiberStrict_disjoint_exceptional {i j : Fin n} (hij : i ≠ j) (idx : FinalIndex.{0} q) :
    Disjoint (Set.range (fiberStrictι (q + 1) n a i).base) (exceptionalSupport q n a j idx) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ hx
  obtain ⟨y, hy⟩ := fiberStrict_projection_mem (q + 1) n a i x
  have hc := exceptionalSupport_projection q n a j idx _ hx
  rw [← hy] at hc
  have h2 := congrArg
    (pullback.snd (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1)).base hc
  rw [horizontalFiber_snd_base, graphPoint_snd] at h2
  exact hij (ha (frobenius_inj k (q + 1) (point_injective h2)))

end Exceptional

end KltDP.Examples.FrobeniusMultiCentreGraphFiber
