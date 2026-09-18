import KltDP.Geometry.SelectedPrimeUnionSmooth
import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.SchematicImageOpenBaseChange

/-!
# The actual selected curve inclusions into the canonical branch scheme

The proved equality of the canonical Cartier ideal with the original
selected union transports the already constructed selected-curve maps.
The resulting closed immersions retain each original surface inclusion.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)
    (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))

/-- The original selected curve maps to the exact canonical Cartier branch scheme. -/
def selectedPrimeCanonicalBranchMap (C : {C : S.PrimeCurve // C ∈ N}) :
    C.val.toScheme ⟶ (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued :=
  S.selectedPrimeUnionCurveMap N C ≫
    eqToHom (congrArg (fun I : S.toScheme.IdealSheafData => I.glueData.glued) hIJ.symm)

@[reassoc]
theorem selectedPrimeCanonicalBranchMap_toBase (C : {C : S.PrimeCurve // C ∈ N}) :
    S.selectedPrimeCanonicalBranchMap N E hE hIJ C ≫
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo = C.val.inclusion := by
  rw [selectedPrimeCanonicalBranchMap, Category.assoc,
    SchematicImageOpenBaseChange.gluedTo_eqToHom, selectedPrimeUnionCurveMap_comp]
  exact hIJ.symm

instance selectedPrimeCanonicalBranchMap_isClosedImmersion
    (C : {C : S.PrimeCurve // C ∈ N}) :
    IsClosedImmersion (S.selectedPrimeCanonicalBranchMap N E hE hIJ C) := by
  dsimp only [selectedPrimeCanonicalBranchMap]
  infer_instance

include hIJ in
/-- The original canonical branch is reduced, derived from the actual selected-ideal equality. -/
theorem canonicalBranch_isReduced_of_selectedIdealEq :
    IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued := by
  rw [hIJ]
  exact (S.selectedPrimeUnionIdeal N).glued_isReduced
    (Scheme.IdealSheafData.vanishingIdeal_support (I := S.selectedPrimeUnionIdeal N)).symm

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedPrimeCanonicalBranchMap_toBase
