import KltDP.Examples.FrobeniusGraphPicardClassLocalEquations

/-!
# The original graph Cartier divisor on its actual complement

The complement frame comes from the literal kernel of an empty source
and the equation 1. Its inverse is therefore the original ideal
inclusion. The actual Over-site generator maps to 1, so the normalized
graph Cartier divisor restricts to zero on this original open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassComplement

open KltDP.Geometry SchemeModuleRestriction
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassDiagonal FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassRational
open FrobeniusGraphPicardClassCartier FrobeniusGraphPicardClassLocalEquations

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

private theorem scalar_one (X : Scheme.{u}) :
    schemeScalarEnd (Y := X) (1 : Γ(X, ⊤)) = 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  let r' : Γ(X, V.unop) := r
  change r' * X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op
    (1 : Γ(X, ⊤)) = r'
  rw [map_one, mul_one]

private theorem complementFrame_inclusion (p : ℕ) :
    (originalOpenFrame (k := k) p none).hom ≫
      (restriction (graphComplement p).ι).map (schemeKernelIdealι (projectiveGraphMorphism p)) ≫
      (restrictionUnitIso (graphComplement p).ι).hom = 𝟙 _ := by
  simp only [originalOpenFrame, complementGlobalFrameIso, localKernelToGlobalPullbackIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← schemeKernelRestrictionIso_hom_ι, Iso.inv_hom_id_assoc,
    asIso_hom, schemeKernelGenerator_comp_ι, scalar_one]
  rfl

private theorem complementFrame_inv (p : ℕ) :
    (originalOpenFrame (k := k) p none).inv =
      (restriction (originalAtlasOpen p none).ι).map
        (schemeKernelIdealι (projectiveGraphMorphism p)) ≫
      (restrictionUnitIso (originalAtlasOpen p none).ι).hom := by
  apply (cancel_epi (originalOpenFrame (k := k) p none).hom).mp
  rw [Iso.hom_inv_id]
  exact (complementFrame_inclusion (k := k) p).symm

-- The existing private inverse-section calculation, specialized to its top Over object.
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

def complementGraphChart (p : ℕ) [Nonempty (graphComplement (k := k) p)] :
    LineBundleTrivializationChart (projectiveProduct k)
      (schemeKernelIdeal (projectiveGraphMorphism p)) where
  openSet := graphComplement p
  nonempty := inferInstance
  trivialization := (openChartToOverUnitIso (graphComplement p)
    (schemeKernelIdeal (projectiveGraphMorphism p)) (originalOpenFrame p none)).symm

/-- The actual complement-frame generator has original inclusion exactly one. -/
theorem complementGraphGenerator_inclusion (p : ℕ) [Nonempty (graphComplement (k := k) p)] :
    (schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op (graphComplement p))
      (lineBundleChartGenerator (projectiveProduct k)
        (schemeKernelIdeal (projectiveGraphMorphism p)) (complementGraphChart p)) =
      (1 : Γ(projectiveProduct k, graphComplement p)) := by
  let X := projectiveProduct k
  let U : X.Opens := graphComplement p
  let M := schemeKernelIdeal (projectiveGraphMorphism (k := k) p)
  let s := lineBundleChartGenerator X M (complementGraphChart p)
  have hs : (openChartToOverUnitIso U M (originalOpenFrame p none)).inv.val.app
      (op (Over.mk (𝟙 U))) s = (1 : Γ(X, U)) :=
    (overTrivializationSectionEquiv X M U
      (complementGraphChart p).trivialization (𝟙 U)).apply_symm_apply (1 : Γ(X, U))
  have H := overFrame_inv_app U M (originalOpenFrame p none) s
  rw [hs, map_one, complementFrame_inv] at H
  change (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) = (U.ι.appIso (U.ι ⁻¹ᵁ U)).hom
    ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op (U.ι ''ᵁ U.ι ⁻¹ᵁ U))
      (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ U) (y := U)
        (Set.image_preimage_subset U.ι.base (U : Set X))).op s)) at H
  rw [Scheme.Opens.ι_appIso] at H
  change (1 : Γ(X, U.ι ''ᵁ U.ι ⁻¹ᵁ U)) =
    (schemeKernelIdealι (projectiveGraphMorphism p)).val.app
    (op (U.ι ''ᵁ U.ι ⁻¹ᵁ U)) (M.val.map
      (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ U) (y := U)
        (Set.image_preimage_subset U.ι.base (U : Set X))).op s) at H
  rw [PresheafOfModules.naturality_apply] at H
  letI : IsIso (U.ι.app U) := Scheme.Hom.isIso_app U.ι U (by simp)
  apply (asIso (U.ι.app U)).commRingCatIsoToRingEquiv.injective
  rw [map_one]
  exact H.symm

/-- The normalized Cartier divisor has equation one on its actual nonempty complement. -/
theorem graphDivisorCandidate_complement (p : ℕ) [Nonempty (graphComplement (k := k) p)] :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show graphComplement p ≤ ⊤ from le_top)).op (graphDivisorCandidate p) = 0 := by
  have hu : graphChartEquationUnit (k := k) p (complementGraphChart p) = 1 := by
    apply Units.ext
    rw [graphChartEquationUnit_val]
    change (projectiveProduct k).germToFunctionField (graphComplement p)
      ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op (graphComplement p))
        (lineBundleChartGenerator (projectiveProduct k)
          (schemeKernelIdeal (projectiveGraphMorphism p)) (complementGraphChart p))) =
      (1 : (projectiveProduct k).functionField)
    rw [complementGraphGenerator_inclusion, map_one]
  have h := graphDivisorCandidate_chart (k := k) p (complementGraphChart p)
  rw [hu] at h
  change _ = cartierEquationClassHom (projectiveProduct k) (graphComplement p) 0 at h
  simpa only [map_zero] using h

end KltDP.Examples.FrobeniusGraphPicardClassComplement
