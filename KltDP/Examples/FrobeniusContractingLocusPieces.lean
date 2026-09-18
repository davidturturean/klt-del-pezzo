import KltDP.Examples.FrobeniusMultiCentreContractingNullLocus
import KltDP.Examples.FrobeniusMultiCentreOldChainGeometry
import KltDP.Geometry.RationalTreePicardClosedImmersionLift
import KltDP.Geometry.RationalTreePicardOfConfiguration

/-!
# The original graph, fibers and old chains inside the actual null locus

Each original reduced closed scheme has support in the independently defined
null locus of the original contracting line bundle. The existing vanishing
ideal and quotient-gluing APIs give its actual factor map. The factors are
closed immersions, their composites are the original surface inclusions,
and their ranges are the inverse images of the original block supports.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusContractingLocusPieces

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreContractingNef FrobeniusMultiCentreContractingNullLocus
  FrobeniusMultiCentreOldChain

section ReducedClosedLift

variable {X W : Scheme.{u}} (Z : Closeds X) (g : W ⟶ X)
  [IsClosedImmersion g] [AlgebraicGeometry.IsReduced W]

private theorem vanishingIdeal_le_ker_of_range_subset
    (h : Set.range g.base ⊆ (Z : Set X)) :
    Scheme.IdealSheafData.vanishingIdeal Z ≤ g.ker := by
  let R : Closeds X := ⟨Set.range g.base, g.isClosedEmbedding.isClosed_range⟩
  exact (Scheme.IdealSheafData.vanishingIdeal_antimono (show R ≤ Z from h)).trans
    (RationalTreePicard.vanishingIdeal_le_ker g R rfl)

private def reducedClosedLift (h : Set.range g.base ⊆ (Z : Set X)) :
    W ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).glueData.glued :=
  RationalTreePicard.liftGluedTo _ g (vanishingIdeal_le_ker_of_range_subset Z g h)

private theorem reducedClosedLift_comp (h : Set.range g.base ⊆ (Z : Set X)) :
    reducedClosedLift Z g h ≫ (Scheme.IdealSheafData.vanishingIdeal Z).gluedTo = g :=
  RationalTreePicard.liftGluedTo_gluedTo _ _ _

end ReducedClosedLift

private theorem range_factor {W Y X : Scheme.{u}}
    (i : W ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (g : W ⟶ X) (h : i ≫ j = g) :
    Set.range i.base = j.base ⁻¹' Set.range g.base := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w, ?_⟩
    change g.base w = (i ≫ j).base w
    rw [h]
  · rintro ⟨w, hw⟩
    refine ⟨w, j.isClosedEmbedding.injective ?_⟩
    change (i ≫ j).base w = j.base y
    rw [h]
    exact hw

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The independently defined null-locus scheme has its original reduced induced structure. -/
instance contractingNullLocus_isReduced : AlgebraicGeometry.IsReduced
    (Positivity.nullLocusScheme (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj)) :=
  (Scheme.IdealSheafData.vanishingIdeal
    (Positivity.nullLocusClosed (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj))).glued_isReduced
    (Scheme.IdealSheafData.vanishingIdeal_support).symm

variable (hn : 2 < n)
include hn

/-- The original graph support lies in the actual null locus. -/
theorem graph_range_subset_nullLocus :
    Set.range (graphStrictι (q + 1) n a).base ⊆
      Positivity.nullLocus (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) := by
  intro x hx
  have h : x ∈ contractingSupport q n a ha hproj := Or.inl (Or.inl hx)
  exact (congrArg (fun T : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme =>
    x ∈ T) (nullLocus_eq_support q n a ha hproj hn)).mpr h

/-- Every original strict-fiber support lies in the actual null locus. -/
theorem fiber_range_subset_nullLocus (i : Fin n) :
    Set.range (fiberStrictι (q + 1) n a i).base ⊆
      Positivity.nullLocus (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) := by
  intro x hx
  have h : x ∈ contractingSupport q n a ha hproj :=
    Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
  exact (congrArg (fun T : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme =>
    x ∈ T) (nullLocus_eq_support q n a ha hproj hn)).mpr h

/-- Each original reduced old-chain support lies in the actual null locus. -/
theorem oldChain_range_subset_nullLocus (i : Fin n) :
    Set.range (oldChainInclusion q n a ha i).base ⊆
      Positivity.nullLocus (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) := by
  intro x hx
  have hxold : x ∈ oldChainSupport q n a i :=
    (congrArg (fun T : Set (multiSurface (q + 1) n a) => x ∈ T)
      (range_oldChainInclusion q n a ha i)).mp hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxold
  have h : x ∈ contractingSupport q n a ha hproj :=
    Or.inr (Set.mem_iUnion₂.mpr ⟨i, j, hj⟩)
  exact (congrArg (fun T : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme =>
    x ∈ T) (nullLocus_eq_support q n a ha hproj hn)).mpr h

/-- The original strict graph as an actual closed subscheme of the actual null locus. -/
def graphToNullLocus : graphStrict (q + 1) n a ⟶
    Positivity.nullLocusScheme (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) :=
  letI := graphStrict_isReduced (q + 1) n a
  reducedClosedLift _ (graphStrictι (q + 1) n a)
    (graph_range_subset_nullLocus q n a ha hproj hn)

@[reassoc] theorem graphToNullLocus_comp : graphToNullLocus q n a ha hproj hn ≫
    Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj) = graphStrictι (q + 1) n a := by
  letI := graphStrict_isReduced (q + 1) n a
  exact reducedClosedLift_comp _ _ _

instance graphToNullLocus_isClosedImmersion :
    IsClosedImmersion (graphToNullLocus q n a ha hproj hn) := by
  haveI : IsClosedImmersion (graphToNullLocus q n a ha hproj hn ≫
      Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)) := by
    rw [graphToNullLocus_comp q n a ha hproj hn]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (Positivity.nullLocusInclusion (multiStructure (q + 1) n a) (contractingLine q n a ha hproj))

/-- An original strict fiber as an actual closed subscheme of the actual null locus. -/
def fiberToNullLocus (i : Fin n) : fiberStrict (q + 1) n a i ⟶
    Positivity.nullLocusScheme (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) :=
  letI := fiberStrict_isReduced (q + 1) n a i
  reducedClosedLift _ (fiberStrictι (q + 1) n a i)
    (fiber_range_subset_nullLocus q n a ha hproj hn i)

@[reassoc] theorem fiberToNullLocus_comp (i : Fin n) : fiberToNullLocus q n a ha hproj hn i ≫
    Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj) = fiberStrictι (q + 1) n a i := by
  letI := fiberStrict_isReduced (q + 1) n a i
  exact reducedClosedLift_comp _ _ _

instance fiberToNullLocus_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (fiberToNullLocus q n a ha hproj hn i) := by
  haveI : IsClosedImmersion (fiberToNullLocus q n a ha hproj hn i ≫
      Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)) := by
    rw [fiberToNullLocus_comp q n a ha hproj hn i]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (Positivity.nullLocusInclusion (multiStructure (q + 1) n a) (contractingLine q n a ha hproj))

/-- An original reduced old exceptional chain as a closed subscheme of the actual null locus. -/
def oldChainToNullLocus (i : Fin n) : oldChain q n a ha i ⟶
    Positivity.nullLocusScheme (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) :=
  reducedClosedLift _ (oldChainInclusion q n a ha i)
    (oldChain_range_subset_nullLocus q n a ha hproj hn i)

@[reassoc] theorem oldChainToNullLocus_comp (i : Fin n) : oldChainToNullLocus q n a ha hproj hn i ≫
    Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj) = oldChainInclusion q n a ha i :=
  reducedClosedLift_comp _ _ _

instance oldChainToNullLocus_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (oldChainToNullLocus q n a ha hproj hn i) := by
  haveI : IsClosedImmersion (oldChainToNullLocus q n a ha hproj hn i ≫
      Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)) := by
    rw [oldChainToNullLocus_comp q n a ha hproj hn i]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (Positivity.nullLocusInclusion (multiStructure (q + 1) n a) (contractingLine q n a ha hproj))

/-- The graph factor has the preimage of the original graph support as its range. -/
theorem range_graphToNullLocus : Set.range (graphToNullLocus q n a ha hproj hn).base =
    (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj)).base ⁻¹' Set.range (graphStrictι (q + 1) n a).base :=
  range_factor _ _ _ (graphToNullLocus_comp q n a ha hproj hn)

/-- Each strict-fiber factor has the preimage of its original support as its range. -/
theorem range_fiberToNullLocus (i : Fin n) : Set.range (fiberToNullLocus q n a ha hproj hn i).base =
    (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj)).base ⁻¹' Set.range (fiberStrictι (q + 1) n a i).base :=
  range_factor _ _ _ (fiberToNullLocus_comp q n a ha hproj hn i)

/-- Each old-chain factor has the preimage of its original old-component union as its range. -/
theorem range_oldChainToNullLocus (i : Fin n) :
    Set.range (oldChainToNullLocus q n a ha hproj hn i).base =
      (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)).base ⁻¹' oldChainSupport q n a i :=
  (range_factor _ _ _ (oldChainToNullLocus_comp q n a ha hproj hn i)).trans
    (congrArg (fun T : Set (multiSurface (q + 1) n a) =>
      (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj)).base ⁻¹' T) (range_oldChainInclusion q n a ha i))

end KltDP.Examples.FrobeniusContractingLocusPieces
