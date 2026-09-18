import KltDP.Geometry.OriginalCartierGlobalRamificationIso

/-!
# Actual branch curves lift into the original ramification locus

The constructed global isomorphism gives a map from each original branch
curve into the unchanged original cover. Its projection is the original
branch inclusion, and an original closed immersion remains closed after
this construction. Disjoint original images stay disjoint in the cover.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance originalCartierRamificationCurveLiftMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued)
    {C : Scheme.{u}} (c : C ⟶ (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued)

/-- The actual branch-curve map lifted through the proved original ramification isomorphism. -/
def ramificationCurveLift : C ⟶ (effectiveCartierQuadraticAtlas X E hE L e).scheme :=
  c ≫ (rootZeroGlobalIsoCanonicalBranch X E hE L e hred).inv ≫
    (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalι

@[reassoc]
theorem ramificationCurveLift_toBase :
    ramificationCurveLift X E hE L e hred c ≫
      (effectiveCartierQuadraticAtlas X E hE L e).morphism =
      c ≫ (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo := by
  rw [ramificationCurveLift, Category.assoc, Category.assoc,
    rootZeroGlobalIsoCanonicalBranch_inv_toBase]

instance ramificationCurveLift_isClosedImmersion [IsClosedImmersion c] :
    IsClosedImmersion (ramificationCurveLift X E hE L e hred c) := by
  letI := (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalι_isClosedImmersion
  dsimp only [ramificationCurveLift]
  infer_instance

/-- The image in the original base is exactly the original branch-curve image. -/
theorem ramificationCurveLift_image_toBase :
    (effectiveCartierQuadraticAtlas X E hE L e).morphism.base ''
      Set.range (ramificationCurveLift X E hE L e hred c).base =
      Set.range (c ≫ (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo).base := by
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_base, ramificationCurveLift_toBase]

/-- Disjoint original branch images give disjoint actual ramification-curve images. -/
theorem disjoint_ramificationCurveLift_ranges
    {C' : Scheme.{u}} (c' : C' ⟶ (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued)
    (hdisj : Disjoint
      (Set.range (c ≫ (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo).base)
      (Set.range (c' ≫ (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo).base)) :
    Disjoint (Set.range (ramificationCurveLift X E hE L e hred c).base)
      (Set.range (ramificationCurveLift X E hE L e hred c').base) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  apply Set.disjoint_left.mp hdisj
  · rw [← ramificationCurveLift_image_toBase X E hE L e hred c]
    exact ⟨z, hz, rfl⟩
  · rw [← ramificationCurveLift_image_toBase X E hE L e hred c']
    exact ⟨z, hz', rfl⟩

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.ramificationCurveLift_toBase
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.ramificationCurveLift_isClosedImmersion
