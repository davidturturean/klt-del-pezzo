import KltDP.Geometry.QuadraticFrameUnitCoordinates
import KltDP.Geometry.QuadraticTensorSectionRestriction
import KltDP.Geometry.QuadraticPulledTensorCoordinates

/-!
# Actual unit roots of the original ambient coefficients

The original pulled matching section, paired in the original ambient
frames, determines the literal coefficient after every base restriction.
Its global frame gives actual units with those squares. Arbitrary original
subopens are retained, including both stages of the actual affine refinement.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.QuadraticAmbientRootUnitSquares

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open TransitionUnitGluing TransitionUnitExtraction RationalTreePicard
open QuadraticFrameUnitCoordinates QuadraticPulledMatchingCoordinates
open QuadraticPulledTensorCoordinates QuadraticTensorSectionRestriction SchemeModuleTensorSections

/-- Original frame units commute with restriction on every actual subopen. -/
theorem unitOn_restrict (Y : Scheme.{u}) (M : Y.Modules)
    (T : KltDP.SheafOfModules.LocalTrivializations (R := Y.ringCatSheaf) M)
    (t : M ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) (b : Γ(Y, ⊤)ˣ)
    (i : T.I) {V W : Y.Opens} (hVW : V ≤ W) (hW : W ≤ T.X i) :
    res Y hVW (unitOn Y M T t b i hW : Γ(Y, W)) =
      (unitOn Y M T t b i (hVW.trans hW) : Γ(Y, V)) := by
  have h := congrArg (res Y hVW) (unitOn_recoveryCoordinate Y M T t b i hW)
  exact h.trans ((res_res Y hVW (le_inf le_top hW) _).trans
    (unitOn_recoveryCoordinate Y M T t b i (hVW.trans hW)).symm)

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type u} (U : ι → X.Opens)
    (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g)
    (hU : (⨆ i, U i) = ⊤)

/-- A global original matching section has the literal pulled chart coefficient. -/
theorem global_pulled_coordinate (q : sections X U g ⊤) (i : ι) :
    chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl
      (((schemeModulePullback f).obj (moduleSheaf X U g)).val.map
        (homOfLE (show f ⁻¹ᵁ U i ≤ ⊤ from le_top)).op
        (pulledSection f (moduleSheaf X U g) ⊤ q)) =
      f.app (U i) (res X (le_inf le_top (le_refl (U i))) (q.val i)) := by
  let c := chartEquiv Y ((schemeModulePullback f).obj (moduleSheaf X U g))
    (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl
  have hs := pulledSection_res f (moduleSheaf X U g)
    (show U i ≤ ⊤ from le_top) q
  have hc' := chartEquiv_pulledSection f U g hc hU i
    (restrict X U g (show U i ≤ ⊤ from le_top) q)
  have hq : trivialization X U g hc i le_rfl
      (restrict X U g (show U i ≤ ⊤ from le_top) q) =
      res X (le_inf le_top (le_refl (U i))) (q.val i) := by
    rw [trivialization_apply, restrict_val, res_res]
  exact (congrArg c hs).trans (hc'.trans (congrArg (f.app (U i)) hq))

variable (t : (schemeModulePullback f).obj (moduleSheaf X U g) ≅
      _root_.SheafOfModules.unit Y.ringCatSheaf) (b : Γ(Y, ⊤)ˣ)
    (q : sections X U (productUnits X U g g) ⊤)
    (hq : pulledSection f (moduleSheaf X U (productUnits X U g g)) ⊤ q =
      (pulledPair f (tensorMultiplication X U g g)).val.app (op (⊤ : Y.Opens))
        (tensorSection ((schemeModulePullback f).obj (moduleSheaf X U g))
          ((schemeModulePullback f).obj (moduleSheaf X U g)) ⊤
          (frameSection Y ((schemeModulePullback f).obj (moduleSheaf X U g)) t b)
          (frameSection Y ((schemeModulePullback f).obj (moduleSheaf X U g)) t b)))

include hq in
/-- The actual pulled ambient chart unit squares to the original mapped coefficient. -/
theorem unitOn_sq (i : ι) :
    (unitOn Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) t b i (W := f ⁻¹ᵁ U i) le_rfl : Γ(Y, f ⁻¹ᵁ U i)) ^ 2 =
      f.app (U i) (res X (le_inf le_top (le_refl (U i))) (q.val i)) := by
  let M := (schemeModulePullback f).obj (moduleSheaf X U g)
  let P := (schemeModulePullback f).obj (moduleSheaf X U (productUnits X U g g))
  let r := frameSection Y M t b
  let m := M.val.map (homOfLE (show f ⁻¹ᵁ U i ≤ ⊤ from le_top)).op r
  let eP := chartEquiv Y P
    (pulledAtlas U (productUnits X U g g) (productUnits_isCocycle X U g g hc hc) f hU)
    i (W := f ⁻¹ᵁ U i) le_rfl
  let c := chartEquiv Y M (pulledAtlas U g hc f hU) i (W := f ⁻¹ᵁ U i) le_rfl m
  have hs := congrArg (P.val.map (homOfLE (show f ⁻¹ᵁ U i ≤ ⊤ from le_top)).op) hq
  have hp := pairing_restrict M M P (pulledPair f (tensorMultiplication X U g g))
    (show f ⁻¹ᵁ U i ≤ ⊤ from le_top) r r
  have he := congrArg eP (hs.trans hp)
  have hleft := global_pulled_coordinate f U (productUnits X U g g)
    (productUnits_isCocycle X U g g hc hc) hU q i
  have hright := pulled_pair_coordinate f U g hc hU i m m
  have hunit := unitOn_val Y M (pulledAtlas U g hc f hU) t b i
    (W := f ⁻¹ᵁ U i) le_rfl
  calc
    _ = c ^ 2 := congrArg (fun z : Γ(Y, f ⁻¹ᵁ U i) => z ^ 2) hunit
    _ = c * c := pow_two c
    _ = _ := hright.symm.trans (he.symm.trans hleft)

include hq in
/-- The unit root formula persists on every subordinate open of the new base. -/
theorem unitOn_sq_subopen (i : ι) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U i) :
    (unitOn Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) t b i (W := V) hV : Γ(Y, V)) ^ 2 =
      f.appLE (U i) V hV (res X (le_inf le_top (le_refl (U i))) (q.val i)) := by
  have hs := congrArg (res Y hV) (unitOn_sq f U g hc hU t b q hq i)
  have hu := unitOn_restrict Y ((schemeModulePullback f).obj (moduleSheaf X U g))
    (pulledAtlas U g hc f hU) t b i hV
    (show f ⁻¹ᵁ U i ≤ (pulledAtlas U g hc f hU).X i from le_rfl)
  exact (congrArg (fun z : Γ(Y, V) => z ^ 2) hu).symm.trans
    ((map_pow (res Y hV) _ 2).symm.trans hs)

include hq in
/-- This is the literal coefficient used by the original affine atlas after base change. -/
theorem unitOn_sq_original_subopen (i : ι) (W : X.Opens) (hW : W ≤ U i)
    (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ W) :
    (unitOn Y ((schemeModulePullback f).obj (moduleSheaf X U g))
      (pulledAtlas U g hc f hU) t b i (W := V)
      (hV.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hW)).le) : Γ(Y, V)) ^ 2 =
      f.appLE W V hV (res X (le_inf le_top hW) (q.val i)) := by
  have he := congrArg (fun z : Γ(X, U i) ⟶ Γ(Y, V) =>
    z (res X (le_inf le_top (le_refl (U i))) (q.val i)))
      (f.map_appLE hV (homOfLE hW).op)
  change f.appLE W V hV (res X hW
    (res X (le_inf le_top (le_refl (U i))) (q.val i))) = _ at he
  rw [res_res] at he
  exact (unitOn_sq_subopen f U g hc hU t b q hq i V
    (hV.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hW)).le)).trans he.symm

end KltDP.Geometry.QuadraticAmbientRootUnitSquares

#print axioms KltDP.Geometry.QuadraticAmbientRootUnitSquares.unitOn_sq_original_subopen
