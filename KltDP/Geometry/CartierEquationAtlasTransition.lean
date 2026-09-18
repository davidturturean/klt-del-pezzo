import KltDP.Geometry.CartierDivisorTrivialization
import KltDP.Geometry.TransitionUnitRecovery

/-!
# Original transition units of an actual Cartier equation atlas

Any covering family of the original equation charts gives an atlas of the
actual module `O(D)`. Its transition unit has the original rational value
`f_i / f_j`, with no sign or effectivity restriction on the divisor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierEquationAtlas

open TransitionUnitGluing TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
  {ι : Type u} (c : ι → CartierEquationChart X D)
  (hc : (Opens.grothendieckTopology X).CoversTop (fun i => (c i).openSet))

/-- The existing equation trivializations on a specified original covering family. -/
def atlas :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf)
      (cartierDivisorModule X D) where
  I := ι
  X i := (c i).openSet
  coversTop := hc
  iso i := _root_.SheafOfModules.freeUniqueIsoUnit
      (R := X.ringCatSheaf.over (c i).openSet) PUnit ≪≫
    cartierEquationOverIso X D (c i).openSet (c i).equation (c i).represents

theorem atlas_unitIso (i : ι) :
    (atlas X D c hc).unitIso i =
      (cartierEquationOverIso X D (c i).openSet (c i).equation (c i).represents).symm := by
  apply Iso.ext
  simp [KltDP.SheafOfModules.LocalTrivializations.unitIso, atlas]

/-- Inverse atlas coordinates are the original section `a / f_i`. -/
theorem chartEquiv_symm_apply (i : ι) {W : X.Opens} (hWi : W ≤ (c i).openSet)
    (a : Γ(X, W)) :
    (chartEquiv X (cartierDivisorModule X D) (atlas X D c hc) i hWi).symm a =
      cartierEquationSectionEquivOn X D (c i).openSet (c i).equation (c i).represents
        (Over.mk (homOfLE hWi)) a := by
  have h := congrArg
    (fun e : (cartierDivisorModule X D).over (c i).openSet ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over (c i).openSet) =>
        e.inv.val.app (op (Over.mk (homOfLE hWi))) a)
    (atlas_unitIso X D c hc i)
  exact (TransitionUnitExtraction.chartEquiv_symm_apply X
    (cartierDivisorModule X D) (atlas X D c hc) i hWi a).trans h

/-- The inverse coordinate formula retains the original rational-function value. -/
theorem chartEquiv_symm_apply_field (i : ι) {W : X.Opens} [Nonempty W]
    (hWi : W ≤ (c i).openSet) (a : Γ(X, W)) :
    rationalFunctionModuleSectionsEquiv X W
        ((chartEquiv X (cartierDivisorModule X D) (atlas X D c hc) i hWi).symm a).val =
      X.germToFunctionField W a * (↑((c i).equation⁻¹) : X.functionField) := by
  letI : Nonempty (Over.mk (homOfLE hWi) : Over (c i).openSet).left :=
    inferInstanceAs (Nonempty W)
  exact (congrArg
    (fun s : (cartierDivisorModule X D).val.obj (op W) =>
      rationalFunctionModuleSectionsEquiv X W s.val)
    (chartEquiv_symm_apply X D c hc i hWi a)).trans
      (cartierEquationSectionEquivOn_apply_field X D (c i).openSet
        (c i).equation (c i).represents (Over.mk (homOfLE hWi)) a)

/-- The extracted original transition unit has rational value `f_i / f_j`. -/
theorem transitionUnits_germ (i j : ι)
    [Nonempty ((c i).openSet ⊓ (c j).openSet : X.Opens)] :
    X.germToFunctionField ((c i).openSet ⊓ (c j).openSet)
        (transitionUnits X (cartierDivisorModule X D) (atlas X D c hc) i j).val =
      (↑((c i).equation / (c j).equation) : X.functionField) := by
  let W : X.Opens := (c i).openSet ⊓ (c j).openSet
  let eᵢ := chartEquiv X (cartierDivisorModule X D) (atlas X D c hc) i
    (inf_le_left : W ≤ (c i).openSet)
  let eⱼ := chartEquiv X (cartierDivisorModule X D) (atlas X D c hc) j
    (inf_le_right : W ≤ (c j).openSet)
  change X.germToFunctionField W (eᵢ (eⱼ.symm 1)) = _
  apply mul_right_cancel₀ (Units.ne_zero ((c i).equation⁻¹))
  calc
    X.germToFunctionField W (eᵢ (eⱼ.symm 1)) *
        (↑((c i).equation⁻¹) : X.functionField) =
        rationalFunctionModuleSectionsEquiv X W (eᵢ.symm (eᵢ (eⱼ.symm 1))).val :=
      (chartEquiv_symm_apply_field X D c hc i inf_le_left (eᵢ (eⱼ.symm 1))).symm
    _ = rationalFunctionModuleSectionsEquiv X W (eⱼ.symm 1).val := by
      rw [eᵢ.symm_apply_apply]
    _ = X.germToFunctionField W 1 * (↑((c j).equation⁻¹) : X.functionField) :=
      chartEquiv_symm_apply_field X D c hc j inf_le_right 1
    _ = (↑((c j).equation⁻¹) : X.functionField) := by rw [map_one, one_mul]
    _ = (↑((c i).equation / (c j).equation) : X.functionField) *
        (↑((c i).equation⁻¹) : X.functionField) := by
      rw [← Units.val_mul]
      congr 1
      rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel, one_mul]

end KltDP.Geometry.CartierEquationAtlas
