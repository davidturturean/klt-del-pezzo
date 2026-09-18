import KltDP.Examples.EqualityAppendixSurface
import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses

/-!
# The original strict transform of the appendix curve Q₁

The initial curve is the actual closed graph `y = x²`. Its puncture away
from `0`, `1`, and `∞` lifts through the original combined blowdown. The
schematic image is the actual strict transform, proved integral here.
No class or local multiplicity is assumed in this construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.EqualityAppendixQ1Construction

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed
  FrobeniusGraphRationalPoints FrobeniusMultiCentreSurface
  FrobeniusContactTowerInfinity FrobeniusStageComplement.PlaneChartedScheme
  EqualityAppendixSurface

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 3]

/-- The original bihomogeneous closure of `y = x²`. -/
abbrev baseCurve : Scheme.{u} := graph (k := k) 2

abbrev baseInclusion : baseCurve (k := k) ⟶ projectiveProduct k := graphι 2

def baseCurveIso : baseCurve (k := k) ≅ projectiveSpace k 1 :=
  graphIsoProjectiveLine 2

/-- The initial graph with the three prescribed centres removed. -/
def puncture : (baseCurve (k := k)).Opens := baseInclusion ⁻¹ᵁ centersComplement

def puncturedCurve : (puncture (k := k)).toScheme ⟶ projectiveProduct k :=
  puncture.ι ≫ baseInclusion

theorem puncturedCurve_range :
    Set.range (puncturedCurve (k := k)).base ⊆ Set.range (centersComplement (k := k)).ι.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨(puncturedCurve (k := k)).base z, z.2⟩, rfl⟩

/-- The point with first coordinate `2` survives the original puncture. -/
theorem puncture_nonempty : Nonempty (puncture (k := k)).toScheme := by
  refine ⟨⟨graphRationalPoint 2 (2 : k), ?_⟩⟩
  change (graphι 2).base (graphRationalPoint 2 (2 : k)) ∈ centersComplement
  rw [graphRationalPoint_ι]
  constructor
  · apply (mem_earlierComplement_iff 3 2 finiteParameters (graphPoint 2 (2 : k))).2
    intro i hi
    have hp := congrArg (firstProjection (k := k)).base hi
    have hcoord : (2 : k) = finiteParameters i :=
      point_injective (by simpa only [graphPoint_fst] using hp)
    have htwo : (2 : k) ≠ 0 := by
      intro h
      have hthree : (3 : k) = 0 := CharP.cast_eq_zero k 3
      have hone : (1 : k) = 0 := by linear_combination hthree - h
      exact one_ne_zero hone
    fin_cases i
    · exact htwo (by simpa only [finiteParameters, Matrix.cons_val_zero] using hcoord)
    · have h : (2 : k) = 1 := by
        simpa only [finiteParameters, Matrix.cons_val_one, Matrix.cons_val_zero] using hcoord
      have hone : (1 : k) = 0 := by linear_combination h
      exact one_ne_zero hone
  · change graphPoint 2 (2 : k) ≠ infinityCenter k
    exact (infinityCenter_ne_graphPoint 2 (2 : k)).symm

theorem puncture_noetherianSpace :
    TopologicalSpace.NoetherianSpace (puncture (k := k)).toScheme := by
  letI := projectiveSpace_noetherianSpace k 1
  exact ((puncture (k := k)).ι ≫ (baseCurveIso (k := k)).hom).isOpenEmbedding.isInducing.noetherianSpace

theorem puncture_isIntegral : IsIntegral (puncture (k := k)).toScheme := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : Nonempty (baseCurve (k := k)) :=
    ⟨(baseCurveIso (k := k)).inv.base (Classical.choice inferInstance)⟩
  letI : IsIntegral (baseCurve (k := k)) :=
    isIntegral_of_isOpenImmersion (baseCurveIso (k := k)).hom
  letI := puncture_nonempty (k := k)
  exact isIntegral_of_isOpenImmersion (puncture (k := k)).ι

/-- The original punctured graph lifted through the actual projection. -/
def lift : (puncture (k := k)).toScheme ⟶ surface (k := k) :=
  letI := projection_restrict_isIso (k := k)
  liftOverIso projection centersComplement puncturedCurve puncturedCurve_range

@[reassoc] theorem lift_projection :
    lift (k := k) ≫ projection = puncturedCurve := by
  letI := projection_restrict_isIso (k := k)
  exact liftOverIso_comp _ _ _ _

/-- The original strict transform, defined by the lifted puncture's kernel. -/
abbrev curve : Scheme.{u} := SchematicImageGlued.image (lift (k := k))

abbrev inclusion : curve (k := k) ⟶ surface (k := k) :=
  SchematicImageGlued.inclusion lift

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion (k := k)) :=
  SchematicImageGlued.inclusion_isClosedImmersion _

theorem range_inclusion :
    Set.range (inclusion (k := k)).base = closure (Set.range (lift (k := k)).base) := by
  letI := puncture_noetherianSpace (k := k)
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact Scheme.Hom.support_ker lift

theorem curve_isReduced : IsReduced (curve (k := k)) := by
  letI := puncture_isIntegral (k := k)
  letI := puncture_noetherianSpace (k := k)
  exact SchematicImageDenseOpen.image_glued_isReduced lift

theorem curve_support_isIrreducible :
    IsIrreducible (((lift (k := k)).ker).support : Set (surface (k := k))) := by
  letI := puncture_isIntegral (k := k)
  letI := puncture_noetherianSpace (k := k)
  rw [Scheme.Hom.support_ker]
  have h := (IrreducibleSpace.isIrreducible_univ (puncture (k := k)).toScheme).image
    (lift (k := k)).base (lift (k := k)).continuous.continuousOn
  simpa only [Set.image_univ] using h.closure

theorem curve_irreducibleSpace : IrreducibleSpace (curve (k := k)) := by
  let I := (lift (k := k)).ker
  letI : IrreducibleSpace I.support :=
    Subtype.irreducibleSpace (curve_support_isIrreducible (k := k))
  apply (irreducibleSpace_def (curve (k := k))).mpr
  have h := (IrreducibleSpace.isIrreducible_univ I.support).image
    I.gluedSupportHomeomorph.symm I.gluedSupportHomeomorph.symm.continuous.continuousOn
  simpa only [Set.image_univ, I.gluedSupportHomeomorph.symm.surjective.range_eq] using h

/-- Integrality is derived from the actual nonempty punctured graph. -/
theorem curve_isIntegral : IsIntegral (curve (k := k)) := by
  letI := curve_isReduced (k := k)
  letI := curve_irreducibleSpace (k := k)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end KltDP.Examples.EqualityAppendixQ1Construction
