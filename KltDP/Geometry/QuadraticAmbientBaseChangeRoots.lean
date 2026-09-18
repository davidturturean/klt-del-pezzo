import KltDP.Geometry.QuadraticAmbientRootUnitSquares
import KltDP.Geometry.QuadraticRefinedPullbackUnits
import KltDP.Geometry.QuadraticPulledRecoverySquare
import KltDP.Geometry.QuadraticCoverAffineBaseChangeAtlas

/-!
# Actual roots in the base-change atlas of the original ambient cover

The original pulled frame and original branch-section coefficient produce
unit roots of the actual base-change atlas. Both the coefficient equations
and the overlap equations use the original ambient affine charts, original
recovery maps and original refined transition units. No splitting, local
root, or tensor compatibility is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.QuadraticAmbientBaseChangeRoots

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open TransitionUnitGluing TransitionUnitExtraction RationalTreePicard InvertibleQuadraticAtlas
open QuadraticFrameUnitCoordinates QuadraticPulledTensorCoordinates SchemeModuleTensorSections
open QuadraticAmbientRootUnitSquares QuadraticRefinedPullbackUnits QuadraticPulledRecoverySquare

/-- The actual original recovery transports the derived frame to the original ambient cocycle sheaf. -/
def recoveredFrame {X Y : Scheme.{u}} (f : Y ⟶ X) (L : InvertibleSheaf X)
    (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) :
    (schemeModulePullback f).obj (moduleSheaf X L.localTrivializations.X
      (invertibleSheafUnits X L)) ≅ _root_.SheafOfModules.unit Y.ringCatSheaf :=
  ((schemeModulePullback f).mapIso (invertibleSheafRecoveryIso X L)).symm ≪≫ t

/-- The actual paired matching section gives roots in precisely the original base-change atlas. -/
theorem baseChange_roots_of_pair {X Y : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
    (f : Y ⟶ X) {ι : Type u} (U : ι → X.Opens) (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ)
    (hc : IsCocycle X U g) (hU : (⨆ i, U i) = ⊤)
    (t : (schemeModulePullback f).obj (moduleSheaf X U g) ≅
      _root_.SheafOfModules.unit Y.ringCatSheaf) (b : Γ(Y, ⊤)ˣ)
    (q : sections X U (productUnits X U g g) ⊤)
    (hq : pulledSection f (moduleSheaf X U (productUnits X U g g)) ⊤ q =
      (pulledPair f (tensorMultiplication X U g g)).val.app (op (⊤ : Y.Opens))
        (tensorSection ((schemeModulePullback f).obj (moduleSheaf X U g))
          ((schemeModulePullback f).obj (moduleSheaf X U g)) ⊤
          (frameSection Y ((schemeModulePullback f).obj (moduleSheaf X U g)) t b)
          (frameSection Y ((schemeModulePullback f).obj (moduleSheaf X U g)) t b))) :
    let D := (fromMatchingSquare X U g hc hU q).baseChangeAtlas f
    ∃ a : ∀ i, Γ(Y, D.opens i)ˣ,
      (∀ i, (a i : Γ(Y, D.opens i)) ^ 2 = D.sections i) ∧
      (∀ i j, res Y (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
        (a i : Γ(Y, D.opens i)) = (D.units i j : Γ(Y, D.opens i ⊓ D.opens j)) *
          res Y inf_le_right (a j : Γ(Y, D.opens j))) := by
  let A := fromMatchingSquare X U g hc hU q
  let D := A.baseChangeAtlas f
  let σ := AffineOpenRefinement.original X U
  let τ := A.baseChangeOriginal f
  let hσ := AffineOpenRefinement.subordinate X U
  let hτ := A.baseChangeSubordinate f
  let a : ∀ i, Γ(Y, D.opens i)ˣ := fun i =>
    unitOn Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) t b (σ (τ i)) (W := D.opens i)
      ((hτ i).trans ((Opens.map f.base).map (homOfLE (hσ (τ i)))).le)
  refine ⟨a, ?_, ?_⟩
  · intro i
    exact unitOn_sq_original_subopen f U g hc hU t b q hq (σ (τ i))
      (A.opens (τ i)) (hσ (τ i)) (D.opens i) (hτ i)
  · intro i j
    exact unitOn_original_overlap f U g (AffineOpenRefinement.opens X U) σ hσ
      (A.baseChangeOpens f) τ hτ hc hU t b i j

/-- The actual branch-frame root yields the required original ambient unit roots. -/
theorem baseChange_roots_of_frame {X Y : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
    (f : Y ⟶ X) (L : InvertibleSheaf X) (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (s : N.val.obj (op (⊤ : X.Opens)))
    (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (b : Γ(Y, ⊤)ˣ)
    (hb : (b : Γ(Y, ⊤)) ^ 2 =
      (UnbranchedRationalBranchRoot.squareFrame f L N e t).hom.val.app (op ⊤)
        (pulledSection f N ⊤ s)) :
    let D := (fromSquareRoot X L N e s).baseChangeAtlas f
    ∃ a : ∀ i, Γ(Y, D.opens i)ˣ,
      (∀ i, (a i : Γ(Y, D.opens i)) ^ 2 = D.sections i) ∧
      (∀ i j, res Y (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
        (a i : Γ(Y, D.opens i)) = (D.units i j : Γ(Y, D.opens i ⊓ D.opens j)) *
          res Y inf_le_right (a j : Γ(Y, D.opens j))) := by
  have hs := pulled_original_square_section f L N e s t b hb
  have hq := pulled_squareCoordinates f L (e.inv.val.app (op ⊤) s)
    (QuadraticGlobalRootCoordinates.rootSection Y (pullbackInvertibleSheaf f L) t b) hs
  exact baseChange_roots_of_pair f L.localTrivializations.X (invertibleSheafUnits X L)
    (invertibleSheafUnits_isCocycle X L) (invertibleSheafUnits_cover X L)
    (recoveredFrame f L t) b (squareCoordinates X L (e.inv.val.app (op ⊤) s)) hq

end KltDP.Geometry.QuadraticAmbientBaseChangeRoots

#print axioms KltDP.Geometry.QuadraticAmbientBaseChangeRoots.baseChange_roots_of_frame
