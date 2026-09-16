import KltDP.Geometry.RationalTreePicardClosedFrameDescent
import KltDP.Geometry.RationalTreePicardClosedLineCoordinates
import KltDP.Geometry.SchemeConormalEquationRestriction

/-!
# The original affine closed-frame trivialization respects open restriction

The two coordinates of the original descent isomorphism are the original
geometric component frames. The unit isomorphism has the right frame as
its actual right pullback, and the left frame after the original scalar
normalization. The same statements hold on every original open, using
the already proved pullback/open-base-change and unit coherence maps.

The restricted component frames below are constructed from the GIVEN
frames. Neither restriction compatibility nor a replacement nodal-chart
realization is assumed. Producing the original component ideals and
frames on a global nodal curve, and global tree gluing, remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry.RationalTreePicard

open SchemeModuleRestriction

section RestrictionCoherence

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
  (M : Y.Modules) (t : M ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf)

/-- Original pullback coordinates commute with actual open restriction.
The equation follows from naturality and the proved unit coherence. -/
theorem openRestriction_pullbackUnitCoordinate :
    (schemeModuleOpenBaseChangeIso f U).hom.app M ≫
        (schemeModulePullback (f ∣_ U)).map
          ((restriction U.ι).map t ≫ (restrictionUnitIso U.ι).hom) ≫
        (schemeModulePullbackUnitIso (f ∣_ U)).hom =
      (restriction (f ⁻¹ᵁ U).ι).map
        ((schemeModulePullback f).map t ≫ (schemeModulePullbackUnitIso f).hom) ≫
        (restrictionUnitIso (f ⁻¹ᵁ U).ι).hom := by
  have hn := (schemeModuleOpenBaseChangeIso f U).hom.naturality t
  change (restriction (f ⁻¹ᵁ U).ι).map ((schemeModulePullback f).map t) ≫
      (schemeModuleOpenBaseChangeIso f U).hom.app
        (_root_.SheafOfModules.unit Y.ringCatSheaf) =
    (schemeModuleOpenBaseChangeIso f U).hom.app M ≫
      (schemeModulePullback (f ∣_ U)).map ((restriction U.ι).map t) at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((schemeModuleOpenBaseChangeIso f U).hom.app M), ← hn]
  simp only [Category.assoc]
  rw [schemeModuleOpenBaseChangeIso_unit]

end RestrictionCoherence

variable (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A]
  [Algebra k A] [Algebra.FiniteType k A]
  (I J : Ideal A) (q : PrimeSpectrum A)
  (hsupport : PrimeSpectrum.zeroLocus (I ⊔ J : Ideal A) = {q})
  [IsReduced (A ⧸ I ⊔ J)]
  (L : InvertibleSheaf (Spec (CommRingCat.of A)))
  (leftFrame : (schemeModulePullback (closedComponentInclusion A I)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)
  (rightFrame : (schemeModulePullback (closedComponentInclusion A J)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf)

/-- The original matching map's first component is the actual geometric
frame map, not merely an abstract module coordinate. -/
theorem closedFrameMatchingSheafMap_leftComponent :
    closedFrameMatchingSheafMap k A I J q hsupport L leftFrame rightFrame ≫
      closedLineLeftComponentMap A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) =
    closedComponentFrameSheafMap A I L leftFrame := by
  have hp : AffineModuleTilde.map (ModuleCat.ofHom
        (closedFrameCoordinatePair A I J L leftFrame rightFrame)) ≫
      AffineModuleTilde.map (ModuleCat.ofHom (LinearMap.fst A (A ⧸ I) (A ⧸ J))) =
    AffineModuleTilde.map (ModuleCat.ofHom
      (closedComponentCoordinate A I L leftFrame)) := by
    rw [← AffineModuleTilde.map_comp]
    rfl
  unfold closedLineLeftComponentMap
  rw [← Category.assoc, closedFrameMatchingSheafMap_ι]
  simp only [Category.assoc]
  rw [← Category.assoc (AffineModuleTilde.map (ModuleCat.ofHom
    (closedFrameCoordinatePair A I J L leftFrame rightFrame))), hp]
  exact (closedComponentFrameSheafMap_eq A I L leftFrame).symm

/-- The second component is the actual original right geometric frame map. -/
theorem closedFrameMatchingSheafMap_rightComponent :
    closedFrameMatchingSheafMap k A I J q hsupport L leftFrame rightFrame ≫
      closedLineRightComponentMap A I J
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) =
    closedComponentFrameSheafMap A J L rightFrame := by
  have hp : AffineModuleTilde.map (ModuleCat.ofHom
        (closedFrameCoordinatePair A I J L leftFrame rightFrame)) ≫
      AffineModuleTilde.map (ModuleCat.ofHom (LinearMap.snd A (A ⧸ I) (A ⧸ J))) =
    AffineModuleTilde.map (ModuleCat.ofHom
      (closedComponentCoordinate A J L rightFrame)) := by
    rw [← AffineModuleTilde.map_comp]
    rfl
  unfold closedLineRightComponentMap
  rw [← Category.assoc, closedFrameMatchingSheafMap_ι]
  simp only [Category.assoc]
  rw [← Category.assoc (AffineModuleTilde.map (ModuleCat.ofHom
    (closedFrameCoordinatePair A I J L leftFrame rightFrame))), hp]
  exact (closedComponentFrameSheafMap_eq A J L rightFrame).symm

variable (hcover : I ⊓ J = ⊥)

/-- Pullback of the ORIGINAL affine unit isomorphism to the right
component is the ORIGINAL right frame, with the canonical unit map. -/
theorem closedFrameUnitIso_pullback_right :
    (schemeModulePullback (closedComponentInclusion A J)).map
        (closedFrameUnitIso k A I J q hsupport L leftFrame rightFrame hcover).hom ≫
      (schemeModulePullbackUnitIso (closedComponentInclusion A J)).hom = rightFrame.hom := by
  apply ((schemeModulePullbackPushforwardAdjunction
    (closedComponentInclusion A J)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [show (schemeModulePullbackUnitIso (closedComponentInclusion A J)).hom =
    schemeModulePullbackUnitHom (closedComponentInclusion A J) from rfl,
    schemeModuleUnit_homEquiv]
  change (closedFrameUnitIso k A I J q hsupport L leftFrame rightFrame hcover).hom ≫
      structureToPushforwardUnit (closedComponentInclusion A J) =
    closedComponentFrameSheafMap A J L rightFrame
  rw [← closedLineUnitIso_rightComponent A I J
    (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) hcover]
  simp only [closedFrameUnitIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [closedFrameDescentSheafIso_hom]
  exact closedFrameMatchingSheafMap_rightComponent k A I J q hsupport L leftFrame rightFrame

/-- The original left pullback becomes the original left frame after
the SAME lifted node scalar that defined the affine matching kernel. -/
theorem closedFrameUnitIso_pullback_left :
    (schemeModulePullback (closedComponentInclusion A I)).map
        (closedFrameUnitIso k A I J q hsupport L leftFrame rightFrame hcover).hom ≫
      (schemeModulePullbackUnitIso (closedComponentInclusion A I)).hom ≫
      schemeScalarEnd (closedLineLeftScalarSection A I
        (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)) = leftFrame.hom := by
  apply ((schemeModulePullbackPushforwardAdjunction
    (closedComponentInclusion A I)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rw [show (schemeModulePullbackUnitIso (closedComponentInclusion A I)).hom =
    schemeModulePullbackUnitHom (closedComponentInclusion A I) from rfl,
    schemeModuleUnit_homEquiv]
  change (closedFrameUnitIso k A I J q hsupport L leftFrame rightFrame hcover).hom ≫
      (structureToPushforwardUnit (closedComponentInclusion A I) ≫
        (schemeModulePushforward (closedComponentInclusion A I)).map
          (schemeScalarEnd (closedLineLeftScalarSection A I
            (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)))) =
    closedComponentFrameSheafMap A I L leftFrame
  rw [← closedLineUnitIso_leftComponent A I J
    (closedFrameScalar k A I J q hsupport L leftFrame rightFrame) hcover]
  simp only [closedFrameUnitIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [closedFrameDescentSheafIso_hom]
  exact closedFrameMatchingSheafMap_leftComponent k A I J q hsupport L leftFrame rightFrame

/-- Actual restriction of the original affine isomorphism to an
arbitrary original open, with the actual source structure-module unit. -/
def closedFrameUnitOpenIso (U : (Spec (CommRingCat.of A)).Opens) :
    (restriction U.ι).obj L.obj ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (restriction U.ι).mapIso
    (closedFrameUnitIso k A I J q hsupport L leftFrame rightFrame hcover) ≪≫
      restrictionUnitIso U.ι

section RestrictedComponent

variable (U : (Spec (CommRingCat.of A)).Opens)

/-- The restricted frame is constructed from the original frame and
the original open-base-change comparison for the original closed component. -/
def closedComponentFrameOpenIso :
    (schemeModulePullback ((closedComponentInclusion A I) ∣_ U)).obj
      ((restriction U.ι).obj L.obj) ≅
    _root_.SheafOfModules.unit
      (((closedComponentInclusion A I) ⁻¹ᵁ U).toScheme.ringCatSheaf) :=
  ((schemeModuleOpenBaseChangeIso (closedComponentInclusion A I) U).app L.obj).symm ≪≫
    (restriction ((closedComponentInclusion A I) ⁻¹ᵁ U).ι).mapIso leftFrame ≪≫
      restrictionUnitIso ((closedComponentInclusion A I) ⁻¹ᵁ U).ι

/-- On EVERY original open, the actual right pullback of the restricted
original trivialization is the constructed restriction of the original right frame. -/
theorem closedFrameUnitOpenIso_pullback_right :
    (schemeModulePullback ((closedComponentInclusion A J) ∣_ U)).map
        (closedFrameUnitOpenIso k A I J q hsupport L leftFrame rightFrame hcover U).hom ≫
      (schemeModulePullbackUnitIso ((closedComponentInclusion A J) ∣_ U)).hom =
    (closedComponentFrameOpenIso A J L rightFrame U).hom := by
  apply (cancel_epi
    ((schemeModuleOpenBaseChangeIso (closedComponentInclusion A J) U).app L.obj).hom).mp
  simp only [closedComponentFrameOpenIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.hom_inv_id_assoc]
  change (schemeModuleOpenBaseChangeIso (closedComponentInclusion A J) U).hom.app L.obj ≫
      (schemeModulePullback ((closedComponentInclusion A J) ∣_ U)).map
        ((restriction U.ι).map
          (closedFrameUnitIso k A I J q hsupport L leftFrame rightFrame hcover).hom ≫
          (restrictionUnitIso U.ι).hom) ≫
        (schemeModulePullbackUnitIso ((closedComponentInclusion A J) ∣_ U)).hom = _
  rw [openRestriction_pullbackUnitCoordinate, closedFrameUnitIso_pullback_right]

/-- The same original left scalar normalization commutes with restriction
to every open, even when the node or an entire component disappears. -/
theorem closedFrameUnitOpenIso_pullback_left :
    (schemeModulePullback ((closedComponentInclusion A I) ∣_ U)).map
        (closedFrameUnitOpenIso k A I J q hsupport L leftFrame rightFrame hcover U).hom ≫
      (schemeModulePullbackUnitIso ((closedComponentInclusion A I) ∣_ U)).hom ≫
      schemeScalarEnd (((closedComponentInclusion A I) ⁻¹ᵁ U).ι.appTop
        (closedLineLeftScalarSection A I
          (closedFrameScalar k A I J q hsupport L leftFrame rightFrame))) =
    (closedComponentFrameOpenIso A I L leftFrame U).hom := by
  apply (cancel_epi
    ((schemeModuleOpenBaseChangeIso (closedComponentInclusion A I) U).app L.obj).hom).mp
  simp only [closedComponentFrameOpenIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.hom_inv_id_assoc]
  let s := closedLineLeftScalarSection A I
    (closedFrameScalar k A I J q hsupport L leftFrame rightFrame)
  let V := (closedComponentInclusion A I) ⁻¹ᵁ U
  let t := (closedFrameUnitIso k A I J q hsupport L leftFrame rightFrame hcover).hom
  change (schemeModuleOpenBaseChangeIso (closedComponentInclusion A I) U).hom.app L.obj ≫
      (schemeModulePullback ((closedComponentInclusion A I) ∣_ U)).map
        ((restriction U.ι).map t ≫ (restrictionUnitIso U.ι).hom) ≫
      (schemeModulePullbackUnitIso ((closedComponentInclusion A I) ∣_ U)).hom ≫
        schemeScalarEnd (V.ι.appTop s) =
    (restriction V.ι).map leftFrame.hom ≫ (restrictionUnitIso V.ι).hom
  calc
    _ = ((restriction V.ι).map
        ((schemeModulePullback (closedComponentInclusion A I)).map t ≫
          (schemeModulePullbackUnitIso (closedComponentInclusion A I)).hom) ≫
        (restrictionUnitIso V.ι).hom) ≫ schemeScalarEnd (V.ι.appTop s) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ schemeScalarEnd (V.ι.appTop s))
        (openRestriction_pullbackUnitCoordinate (closedComponentInclusion A I) U L.obj t)
    _ = (restriction V.ι).map
        ((schemeModulePullback (closedComponentInclusion A I)).map t ≫
          (schemeModulePullbackUnitIso (closedComponentInclusion A I)).hom) ≫
        (restriction V.ι).map (schemeScalarEnd s) ≫ (restrictionUnitIso V.ι).hom := by
      rw [Category.assoc, ← restriction_schemeScalarEnd V s]
    _ = (restriction V.ι).map
        (((schemeModulePullback (closedComponentInclusion A I)).map t ≫
          (schemeModulePullbackUnitIso (closedComponentInclusion A I)).hom) ≫
            schemeScalarEnd s) ≫ (restrictionUnitIso V.ι).hom := by
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [Category.assoc, closedFrameUnitIso_pullback_left]

end RestrictedComponent

end KltDP.Geometry.RationalTreePicard
