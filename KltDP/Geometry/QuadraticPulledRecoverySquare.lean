import KltDP.Geometry.QuadraticPulledTensorCoordinates
import KltDP.Geometry.SchemeModulePullbackTensorNaturality
import KltDP.Geometry.UnbranchedRationalQuadraticCoordinates

/-!
# The original recovered quadratic section after actual pullback

The original pullback tensor comparison is natural for the original
recovery maps. Consequently a square root in the pulled half-line gives
a square root for the original ambient matching section, evaluated using
the original pulled multiplication. The final statement uses the actual
canonical-section frame coefficient and derives every tensor equality.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.QuadraticPulledRecoverySquare

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open SchemeModuleTensorSections RationalTreePicard
open SchemeModulePullbackTensorSectionUnits QuadraticPulledTensorCoordinates
open InvertibleQuadraticAtlas TransitionUnitGluing TransitionUnitExtraction
open UnbranchedRationalQuadraticCoordinates QuadraticGlobalRootCoordinates

/-- The original pulled pairing retains the original changes of module coordinates. -/
theorem pulledPair_precompose {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N M' N' P : X.Modules} (g : M ⟶ M') (h : N ⟶ N') (q : M' ⊗ N' ⟶ P) :
    pulledPair f ((g ⊗ h) ≫ q) =
      ((schemeModulePullback f).map g ⊗ (schemeModulePullback f).map h) ≫
        pulledPair f q := by
  apply (cancel_epi (schemeModulePullbackTensorIso f M N).hom).mp
  simp only [pulledPair, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← schemeModulePullbackTensorIso_natural_assoc f g h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Naturality on actual local section pairs, with modules kept abstract. -/
theorem pulledPair_precompose_apply {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N M' N' P : X.Modules} (g : M ⟶ M') (h : N ⟶ N') (q : M' ⊗ N' ⟶ P)
    (W : Y.Opens) (m : ((schemeModulePullback f).obj M).val.obj (op W))
    (n : ((schemeModulePullback f).obj N).val.obj (op W)) :
    (pulledPair f ((g ⊗ h) ≫ q)).val.app (op W)
      (tensorSection ((schemeModulePullback f).obj M) ((schemeModulePullback f).obj N)
        W m n) =
      (pulledPair f q).val.app (op W)
        (tensorSection ((schemeModulePullback f).obj M') ((schemeModulePullback f).obj N')
          W (((schemeModulePullback f).map g).val.app (op W) m)
          (((schemeModulePullback f).map h).val.app (op W) n)) := by
  rw [pulledPair_precompose]
  change (pulledPair f q).val.app (op W)
    ((((schemeModulePullback f).map g ⊗ (schemeModulePullback f).map h).val.app (op W))
      (tensorSection _ _ W m n)) = _
  rw [tensorSection_natural]

/-- An actual tensor square transports through the original pulled pairing. -/
theorem pulled_pair_of_tensor {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N P : X.Modules} (q : M ⊗ N ⟶ P) (W : X.Opens)
    (s : (M ⊗ N).val.obj (op W))
    (m : ((schemeModulePullback f).obj M).val.obj (op (f ⁻¹ᵁ W)))
    (n : ((schemeModulePullback f).obj N).val.obj (op (f ⁻¹ᵁ W)))
    (hs : (schemeModulePullbackTensorIso f M N).hom.val.app (op (f ⁻¹ᵁ W))
      (pulledSection f (M ⊗ N) W s) =
        tensorSection ((schemeModulePullback f).obj M) ((schemeModulePullback f).obj N)
          (f ⁻¹ᵁ W) m n) :
    pulledSection f P W (q.val.app (op W) s) =
      (pulledPair f q).val.app (op (f ⁻¹ᵁ W))
        (tensorSection ((schemeModulePullback f).obj M) ((schemeModulePullback f).obj N)
          (f ⁻¹ᵁ W) m n) := by
  let T := schemeModulePullbackTensorIso f M N
  let z := pulledSection f (M ⊗ N) W s
  have hc : T.inv.val.app (op (f ⁻¹ᵁ W)) (T.hom.val.app (op (f ⁻¹ᵁ W)) z) = z :=
    congrArg (fun v : (schemeModulePullback f).obj (M ⊗ N) ⟶
      (schemeModulePullback f).obj (M ⊗ N) => v.val.app (op (f ⁻¹ᵁ W)) z) T.hom_inv_id
  have hi := (congrArg (T.inv.val.app (op (f ⁻¹ᵁ W))) hs).symm.trans hc
  change _ = ((schemeModulePullback f).map q).val.app (op (f ⁻¹ᵁ W))
    (T.inv.val.app (op (f ⁻¹ᵁ W)) _)
  rw [hi]
  exact (pullback_map_unit f q W s).symm

/-- The original ambient matching section is the square of the recovered root. -/
theorem pulled_squareCoordinates {X Y : Scheme.{u}} (f : Y ⟶ X) (L : InvertibleSheaf X)
    (s : (L.obj ⊗ L.obj).val.obj (op (⊤ : X.Opens)))
    (r : ((schemeModulePullback f).obj L.obj).val.obj (op (⊤ : Y.Opens)))
    (hs : (schemeModulePullbackTensorIso f L.obj L.obj).hom.val.app (op (⊤ : Y.Opens))
      (pulledSection f (L.obj ⊗ L.obj) ⊤ s) =
        tensorSection ((schemeModulePullback f).obj L.obj)
          ((schemeModulePullback f).obj L.obj) ⊤ r r) :
    pulledSection f
      (moduleSheaf X L.localTrivializations.X
        (productUnits X L.localTrivializations.X (invertibleSheafUnits X L)
          (invertibleSheafUnits X L))) ⊤ (squareCoordinates X L s) =
      (pulledPair f (tensorMultiplication X L.localTrivializations.X
        (invertibleSheafUnits X L) (invertibleSheafUnits X L))).val.app (op (⊤ : Y.Opens))
        (tensorSection
          ((schemeModulePullback f).obj (moduleSheaf X L.localTrivializations.X
            (invertibleSheafUnits X L)))
          ((schemeModulePullback f).obj (moduleSheaf X L.localTrivializations.X
            (invertibleSheafUnits X L))) ⊤
          (((schemeModulePullback f).map (invertibleSheafRecoveryIso X L).hom).val.app (op ⊤) r)
          (((schemeModulePullback f).map (invertibleSheafRecoveryIso X L).hom).val.app (op ⊤) r)) := by
  exact (pulled_pair_of_tensor f (squareCoordinatesIso X L).hom ⊤ s r r hs).trans
    (pulledPair_precompose_apply f (invertibleSheafRecoveryIso X L).hom
      (invertibleSheafRecoveryIso X L).hom
      (tensorMultiplication X L.localTrivializations.X
        (invertibleSheafUnits X L) (invertibleSheafUnits X L)) ⊤ r r)

/-- The actual branch frame coefficient supplies the tensor equality required above. -/
theorem pulled_original_square_section {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : InvertibleSheaf X) (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (s : N.val.obj (op (⊤ : X.Opens)))
    (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (b : Γ(Y, ⊤)ˣ)
    (hb : (b : Γ(Y, ⊤)) ^ 2 =
      (UnbranchedRationalBranchRoot.squareFrame f L N e t).hom.val.app (op ⊤)
        (pulledSection f N ⊤ s)) :
    (schemeModulePullbackTensorIso f L.obj L.obj).hom.val.app (op (⊤ : Y.Opens))
      (pulledSection f (L.obj ⊗ L.obj) ⊤ (e.inv.val.app (op ⊤) s)) =
      tensorSection (pullbackInvertibleSheaf f L).obj (pullbackInvertibleSheaf f L).obj ⊤
        (rootSection Y (pullbackInvertibleSheaf f L) t b)
        (rootSection Y (pullbackInvertibleSheaf f L) t b) := by
  have h := pulled_square_section_eq f L N e (pulledSection f N ⊤ s) t b hb
  change (schemeModulePullbackTensorIso f L.obj L.obj).hom.val.app (op (⊤ : Y.Opens))
    (((schemeModulePullback f).map e.inv).val.app (op (⊤ : Y.Opens))
      (pulledSection f N ⊤ s)) = _ at h
  exact (congrArg
    ((schemeModulePullbackTensorIso f L.obj L.obj).hom.val.app (op (⊤ : Y.Opens)))
      (pullback_map_unit f e.inv ⊤ s)).symm.trans h

end KltDP.Geometry.QuadraticPulledRecoverySquare

#print axioms KltDP.Geometry.QuadraticPulledRecoverySquare.pulled_squareCoordinates
