import KltDP.Geometry.OriginalQuadraticCoverEuler
import KltDP.Geometry.PointBlowupSequenceCohomologyLiteralUse
import KltDP.Geometry.MinimalResolutionQuadraticRegular
import KltDP.Geometry.IsolatedExceptionalSelectionGeometry

/-!
# Euler characteristic after the original selected-cover blowdowns

The original cover's proved Euler formula and cohomology invariance of
the same actual blowup sequence give the target's Euler characteristic.
The target's smoothness is derived from its actual regular points. The
original source Euler characteristic is retained without a rationality
or structure-sheaf vanishing hypothesis.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (hiso : IsolatedSelection π N) (hN : ∀ C ∈ N, IsExceptionalCurve π C)

local instance selectedCoverBlowdownEulerSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedCoverBlowdownEulerMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

include hklt hiso hN

/-- The original cover and the same sequence determine the actual target Euler value. -/
theorem selectedCover_blowdown_euler
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hmin.regular = -2)
    (V : NormalProjectiveSurface k) (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
    (b : (OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne).toScheme ⟶ V.toScheme)
    (hseq : IsPointBlowupSequence
      (OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne) V b) :
    (eulerCharacteristic V.structureMorphism (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) : ℚ) =
      2 * (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) - (N.card : ℚ) / 4 := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  letI : IsSmoothOfRelativeDimension 2 V.structureMorphism :=
    V.isSmoothOfRelativeDimension_two_of_regularPoints hV
  letI : IsSmooth V.structureMorphism := IsSmoothOfRelativeDimension.isSmooth 2 V.structureMorphism
  let Y := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
  have hY : (eulerCharacteristic Y.structureMorphism
      (_root_.SheafOfModules.unit Y.toScheme.ringCatSheaf) : ℚ) =
      2 * (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) - (N.card : ℚ) / 4 :=
    S.selectedOriginalCover_eulerCharacteristic N E hE L e hweil
      (isolatedSelection_pairwise π N hiso hN)
      (selectedExceptional_projectiveLine π N hmin hklt hN) hself
  calc
    _ = (eulerCharacteristic Y.structureMorphism
        (_root_.SheafOfModules.unit Y.toScheme.ringCatSheaf) : ℚ) :=
      congrArg (fun z : ℤ => (z : ℚ)) (NativePointBlowupCohomology.sequence_euler_eq hseq).symm
    _ = _ := hY

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.selectedCover_blowdown_euler
