import KltDP.Geometry.OriginalCartierRootZeroBranchMap
import KltDP.Geometry.SchematicImageOpenBaseChange

/-!
# The original global ramification is the original canonical Cartier branch

The already constructed global branch map is a surjective closed
immersion. Reducedness of the actual original Cartier branch makes it an
isomorphism. The existing equality with the canonical regular-equation
ideal then transports only the branch model, retaining the original
global ramification scheme and both original projection equations.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]

local instance originalCartierGlobalRamificationIsoMonoidal : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued)

/-- The actual global root-zero scheme is isomorphic to the original canonical Cartier branch. -/
def rootZeroGlobalIsoCanonicalBranch :
    (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalScheme ≅
      (effectiveCartierIdealDataOfRegularEquations X E hE).glueData.glued := by
  letI : IsReduced (effectiveCartierIdealData X E hE L e).glueData.glued := by
    rw [effectiveCartierIdealData_eq_ofRegularEquations X E hE L e]
    exact hred
  letI : IsIso (rootZeroGlobalBranchMap X E hE L e) :=
    isIso_of_isClosedImmersion_of_surjective _
  exact asIso (rootZeroGlobalBranchMap X E hE L e) ≪≫
    eqToIso (congrArg (fun I : X.IdealSheafData => I.glueData.glued)
      (effectiveCartierIdealData_eq_ofRegularEquations X E hE L e))

@[reassoc]
theorem rootZeroGlobalIsoCanonicalBranch_hom_toBase :
    (rootZeroGlobalIsoCanonicalBranch X E hE L e hred).hom ≫
      (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo =
      (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalι ≫
        (effectiveCartierQuadraticAtlas X E hE L e).morphism := by
  change (rootZeroGlobalBranchMap X E hE L e ≫
    eqToHom (congrArg (fun I : X.IdealSheafData => I.glueData.glued)
      (effectiveCartierIdealData_eq_ofRegularEquations X E hE L e))) ≫ _ = _
  rw [Category.assoc, SchematicImageOpenBaseChange.gluedTo_eqToHom,
    rootZeroGlobalBranchMap_toBase]
  exact effectiveCartierIdealData_eq_ofRegularEquations X E hE L e

@[reassoc]
theorem rootZeroGlobalIsoCanonicalBranch_inv_toBase :
    (rootZeroGlobalIsoCanonicalBranch X E hE L e hred).inv ≫
      (effectiveCartierQuadraticAtlas X E hE L e).rootZeroGlobalι ≫
        (effectiveCartierQuadraticAtlas X E hE L e).morphism =
      (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo := by
  rw [← rootZeroGlobalIsoCanonicalBranch_hom_toBase X E hE L e hred,
    Iso.inv_hom_id_assoc]

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.rootZeroGlobalIsoCanonicalBranch
#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.rootZeroGlobalIsoCanonicalBranch_hom_toBase
