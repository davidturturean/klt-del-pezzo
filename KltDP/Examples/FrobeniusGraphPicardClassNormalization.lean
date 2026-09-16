import KltDP.Examples.FrobeniusGraphPicardClassInclusion

/-!
# Original graph-frame generators under the original ideal inclusion

The restriction/pullback comparisons cancel before any section is
evaluated. The actual Over-site generator therefore maps to the
original diagonal graph equation, with no choice of a unit factor.
This identifies the scale in the rational inclusion formula with the
previously constructed graph function.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassNormalization

open KltDP.Geometry SchemeModuleRestriction
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRational FrobeniusGraphPicardClassCartier
open FrobeniusGraphPicardClassInclusion

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

private theorem originalDiagonalFrame_eq (p : ℕ) (i : Fin 2) :
    originalOpenFrame (k := k) p (some i) =
      diagonalLocalFrameIso p i ≪≫
        (schemeKernelRestrictionIso (projectiveGraphMorphism p) (diagonalOpen i)).symm := by
  apply Iso.ext
  simp only [originalOpenFrame, diagonalGlobalFrameIso, localKernelToGlobalPullbackIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Category.comp_id]

private theorem originalDiagonalFrame_inclusion (p : ℕ) (i : Fin 2) :
    (originalOpenFrame (k := k) p (some i)).hom ≫
      (restriction (diagonalOpen (k := k) i).ι).map
        (schemeKernelIdealι (projectiveGraphMorphism (k := k) p)) ≫
      (restrictionUnitIso (diagonalOpen (k := k) i).ι).hom =
        schemeScalarEnd (Y := (diagonalOpen (k := k) i).toScheme)
          (diagonalEquation (k := k) p i) := by
  rw [originalDiagonalFrame_eq, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← schemeKernelRestrictionIso_hom_ι, Iso.inv_hom_id_assoc]
  exact schemeKernelGenerator_comp_ι (projectiveGraphMorphism p ∣_ diagonalOpen i)
    (diagonalEquation p i) (diagonalEquation_eq_zero p i)

-- A bounded copy of the existing private original-map calculation in
-- OpenFrameTransitionCoefficient; the original declaration is not referenced.
private theorem overFrame_inv_app {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (s : M.val.obj (op U)) :
    U.ι.app U ((openChartToOverUnitIso U M e).inv.val.app (op (Over.mk (𝟙 U))) s) =
      e.inv.val.app (op (U.ι ⁻¹ᵁ U))
        (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ U) (y := U)
          (Set.image_preimage_subset U.ι.base (U : Set X))).op s) := by
  letI : IsIso (U.ι.app U) := Scheme.Hom.isIso_app U.ι U (by simp)
  change (asIso (U.ι.app U)).hom ((asIso (U.ι.app U)).inv
    (e.inv.val.app (op (U.ι ⁻¹ᵁ U))
      (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ U) (y := U)
        (Set.image_preimage_subset U.ι.base (U : Set X))).op s))) = _
  exact Iso.inv_hom_id_apply _ _

def diagonalGraphChart (p : ℕ) (i : Fin 2) :
    LineBundleTrivializationChart (projectiveProduct k)
      (schemeKernelIdeal (projectiveGraphMorphism p)) where
  openSet := diagonalOpen i
  nonempty := inferInstance
  trivialization := (openChartToOverUnitIso (diagonalOpen i)
    (schemeKernelIdeal (projectiveGraphMorphism p)) (originalOpenFrame p (some i))).symm

def diagonalGraphGenerator (p : ℕ) (i : Fin 2) :
    (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)).val.obj (op (diagonalOpen i)) :=
  lineBundleChartGenerator (projectiveProduct k)
    (schemeKernelIdeal (projectiveGraphMorphism p)) (diagonalGraphChart p i)

/-- Each actual Over-site generator maps to the original diagonal equation. -/
theorem diagonalGraphGenerator_inclusion (p : ℕ) (i : Fin 2) :
    (schemeKernelIdealι (projectiveGraphMorphism (k := k) p)).val.app
      (op (diagonalOpen (k := k) i)) (diagonalGraphGenerator (k := k) p i) =
        diagonalSection (k := k) p i := by
  let X := projectiveProduct k
  let U : X.Opens := diagonalOpen (k := k) i
  let M := schemeKernelIdeal (projectiveGraphMorphism (k := k) p)
  let e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M :=
    originalOpenFrame (k := k) p (some i)
  let s : M.val.obj (op U) := diagonalGraphGenerator (k := k) p i
  let V : U.toScheme.Opens := U.ι ⁻¹ᵁ U
  let j : U.ι ''ᵁ V ⟶ U := homOfLE (Set.image_preimage_subset U.ι.base (U : Set X))
  let t : ((restriction U.ι).obj M).val.obj (op V) := M.val.map j.op s
  have hs : (openChartToOverUnitIso U M e).inv.val.app (op (Over.mk (𝟙 U))) s =
      (1 : Γ(X, U)) := by
    exact (overTrivializationSectionEquiv X M U
      (diagonalGraphChart (k := k) p i).trivialization (𝟙 U)).apply_symm_apply (1 : Γ(X, U))
  have ht : e.inv.val.app (op V) t = (1 : Γ(U.toScheme, V)) := by
    have H := overFrame_inv_app U M e s
    rw [hs, map_one] at H
    exact H.symm
  have hte : t = e.hom.val.app (op V) (1 : Γ(U.toScheme, V)) := by
    let ε := ((_root_.SheafOfModules.evaluation U.toScheme.ringCatSheaf (op V)).mapIso e).toLinearEquiv
    change t = ε (1 : Γ(U.toScheme, V))
    apply ε.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    exact ht
  have H := congrArg (fun a : End (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf) =>
    a.val.app (op V) (1 : Γ(U.toScheme, V))) (originalDiagonalFrame_inclusion (k := k) p i)
  change (restrictionUnitIso U.ι).hom.val.app (op V)
      ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op (U.ι ''ᵁ V))
        (e.hom.val.app (op V) (1 : Γ(U.toScheme, V)))) = _ at H
  rw [← hte] at H
  change (U.ι.appIso V).hom
      ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op (U.ι ''ᵁ V))
        (M.val.map j.op s)) = (schemeScalarEnd (Y := U.toScheme) (diagonalEquation (k := k) p i)).val.app
          (op V) (1 : Γ(U.toScheme, V)) at H
  rw [Scheme.Opens.ι_appIso] at H
  change (schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op (U.ι ''ᵁ V))
      (M.val.map j.op s) = (schemeScalarEnd (Y := U.toScheme) (diagonalEquation (k := k) p i)).val.app
          (op V) (1 : Γ(U.toScheme, V)) at H
  rw [PresheafOfModules.naturality_apply, schemeScalarEnd_app, one_mul] at H
  have hres : U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
      (diagonalEquation (k := k) p i) = U.ι.app U (diagonalSection (k := k) p i) := by
    simp only [diagonalEquation, Scheme.Opens.topIso_inv,
      Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.ι_app]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [hres] at H
  letI : IsIso (U.ι.app U) := Scheme.Hom.isIso_app U.ι U (by simp)
  exact (asIso (U.ι.app U)).commRingCatIsoToRingEquiv.injective H

/-- The normalizing value is exactly the original graph equation's germ. -/
theorem firstGraphGeneratorValue_eq_graphFunction (p : ℕ) :
    firstGraphGeneratorValue (k := k) p = graphFunction p := by
  change (projectiveProduct k).germToFunctionField (diagonalOpen 0)
      ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op (diagonalOpen 0))
        (diagonalGraphGenerator p 0)) = _
  rw [diagonalGraphGenerator_inclusion, graphFunction_eq_original_section]

/-- The actual inclusion normalization now has its original prescribed graph function. -/
theorem graphInclusion_graphFunction_factor (p : ℕ) (V : (projectiveProduct k).Opens)
    [Nonempty V]
    (s : (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)).val.obj (op V)) :
    (projectiveProduct k).germToFunctionField V
        ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op V) s) =
      graphFunction p * lineBundleGenericCoordinate (projectiveProduct k)
        (schemeKernelIdeal (projectiveGraphMorphism p)) (diagonalOpen 0)
        (firstGraphTrivialization p) V s := by
  rw [graphInclusion_generic_factor, firstGraphGeneratorValue_eq_graphFunction]

end KltDP.Examples.FrobeniusGraphPicardClassNormalization
