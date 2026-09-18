import KltDP.Geometry.QuadraticTensorPairingFrame
import KltDP.Geometry.QuadraticPulledMatchingCoordinates
import KltDP.Geometry.SchemeModulePullbackTensorSections

/-!
# Original pulled quadratic tensor multiplication in ambient frames

The actual pulled multiplication sends the original pulled frame pair
to the original product frame. Its coordinate on every section pair is
therefore the product of their original ambient-frame coordinates. The
pullback tensor comparison and all section maps are retained literally.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.QuadraticPulledTensorCoordinates

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open SchemeModuleTensorSections RationalTreePicard
open SchemeModulePullbackTensorSectionUnits SchemeModulePullbackTensorSections

/-- The original inverse tensor comparison followed by the actual pulled pairing. -/
def pulledPair {X Y : Scheme.{u}} (f : Y ⟶ X) {M N P : X.Modules} (q : M ⊗ N ⟶ P) :
    (schemeModulePullback f).obj M ⊗ (schemeModulePullback f).obj N ⟶
      (schemeModulePullback f).obj P :=
  (schemeModulePullbackTensorIso f M N).inv ≫ (schemeModulePullback f).map q

/-- The actual pulled pairing preserves original adjunction-unit section pairs. -/
theorem pulledPair_pulledSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N P : X.Modules} (q : M ⊗ N ⟶ P) (W : X.Opens)
    (m : M.val.obj (op W)) (n : N.val.obj (op W)) :
    (pulledPair f q).val.app (op (f ⁻¹ᵁ W))
      (tensorSection ((schemeModulePullback f).obj M) ((schemeModulePullback f).obj N)
        (f ⁻¹ᵁ W) (pulledSection f M W m) (pulledSection f N W n)) =
      pulledSection f P W (q.val.app (op W) (tensorSection M N W m n)) := by
  let T := schemeModulePullbackTensorIso f M N
  let z := pulledSection f (M ⊗ N) W (tensorSection M N W m n)
  have hT := tensor_unit_section f M N W m n
  have hc : T.inv.val.app (op (f ⁻¹ᵁ W)) (T.hom.val.app (op (f ⁻¹ᵁ W)) z) = z :=
    congrArg (fun v : (schemeModulePullback f).obj (M ⊗ N) ⟶
      (schemeModulePullback f).obj (M ⊗ N) => v.val.app (op (f ⁻¹ᵁ W)) z) T.hom_inv_id
  have hi := (congrArg (T.inv.val.app (op (f ⁻¹ᵁ W))) hT).symm.trans hc
  change ((schemeModulePullback f).map q).val.app (op (f ⁻¹ᵁ W))
    (T.inv.val.app (op (f ⁻¹ᵁ W)) _) = _
  exact (congrArg (((schemeModulePullback f).map q).val.app (op (f ⁻¹ᵁ W))) hi).trans
    (pullback_map_unit f q W (tensorSection M N W m n))

open TransitionUnitGluing TransitionUnitExtraction QuadraticTensorSectionCoordinates

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g)
    (hU : (⨆ i, U i) = ⊤)

/-- The original pulled ambient frame pair has product-frame coordinate one. -/
theorem pulled_pair_frame (i : ι) :
    chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U (productUnits X U g g)))
      (pulledAtlas U (productUnits X U g g) (productUnits_isCocycle X U g g hc hc) f hU)
      i (W := f ⁻¹ᵁ U i) le_rfl
      ((pulledPair f (tensorMultiplication X U g g)).val.app (op (f ⁻¹ᵁ U i))
        (tensorSection ((schemeModulePullback f).obj (moduleSheaf X U g))
          ((schemeModulePullback f).obj (moduleSheaf X U g)) (f ⁻¹ᵁ U i)
          (pulledFrame U g hc f i) (pulledFrame U g hc f i))) = 1 := by
  let σ := chartFrame U g hc i
  have hp := pulledPair_pulledSection f (tensorMultiplication X U g g) (U i) σ σ
  have hs := tensorMultiplication_tensorSection X U g g (U i) σ σ
  have hp' := hp.trans (congrArg (pulledSection f
    (moduleSheaf X U (productUnits X U g g)) (U i)) hs)
  have hc' := QuadraticPulledMatchingCoordinates.chartEquiv_pulledSection f U
    (productUnits X U g g) (productUnits_isCocycle X U g g hc hc) hU i
    (sectionMul X U g g (U i) σ σ)
  have hone : trivialization X U (productUnits X U g g)
      (productUnits_isCocycle X U g g hc hc) i le_rfl
      (sectionMul X U g g (U i) σ σ) = 1 := by
    rw [sectionMul_trivialization, trivialization_chartFrame, one_mul]
  rw [hone, map_one] at hc'
  exact (congrArg (chartEquiv Y
    ((schemeModulePullback f).obj (moduleSheaf X U (productUnits X U g g)))
    (pulledAtlas U (productUnits X U g g) (productUnits_isCocycle X U g g hc hc) f hU)
    i (W := f ⁻¹ᵁ U i) le_rfl) hp').trans hc'

/-- The original pulled multiplication has product coordinates on every section pair. -/
theorem pulled_pair_coordinate (i : ι)
    (m n : ((schemeModulePullback f).obj (moduleSheaf X U g)).val.obj (op (f ⁻¹ᵁ U i))) :
    chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U (productUnits X U g g)))
      (pulledAtlas U (productUnits X U g g) (productUnits_isCocycle X U g g hc hc) f hU)
      i (W := f ⁻¹ᵁ U i) le_rfl
      ((pulledPair f (tensorMultiplication X U g g)).val.app (op (f ⁻¹ᵁ U i))
        (tensorSection ((schemeModulePullback f).obj (moduleSheaf X U g))
          ((schemeModulePullback f).obj (moduleSheaf X U g)) (f ⁻¹ᵁ U i) m n)) =
      chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U g))
        (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl m *
      chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U g))
        (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl n := by
  let M := (schemeModulePullback f).obj (moduleSheaf X U g)
  let P := (schemeModulePullback f).obj (moduleSheaf X U (productUnits X U g g))
  let eM := chartEquiv Y M (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl
  let eP := chartEquiv Y P
    (pulledAtlas U (productUnits X U g g) (productUnits_isCocycle X U g g hc hc) f hU)
    i (W := f ⁻¹ᵁ U i) le_rfl
  have he : eM.symm (1 : Γ(Y, f ⁻¹ᵁ U i)) = pulledFrame U g hc f i := by
    apply eM.injective
    exact (eM.apply_symm_apply 1).trans (pulledFrameCoordinate f U g hc hU i).symm
  apply QuadraticTensorPairingFrame.coordinate M M P
    (pulledPair f (tensorMultiplication X U g g)) (f ⁻¹ᵁ U i) eM eM eP _ m n
  rw [he]
  exact pulled_pair_frame f U g hc hU i

end KltDP.Geometry.QuadraticPulledTensorCoordinates

#print axioms KltDP.Geometry.QuadraticPulledTensorCoordinates.pulled_pair_coordinate
