import KltDP.Geometry.RationalTreePicardClosedFrameMatching
import KltDP.Geometry.AffineModuleTildePullbackComp

/-!
# Original closed-component coordinates are geometric frame maps

The coordinate of an original global section was defined by tensor
extension and tilde full faithfulness. Here it is identified with the
adjunction transpose of the GIVEN geometric frame of the original closed
component pullback. The proof uses the original pullback comparison's
tensor-unit normalization, not a supplied coordinate compatibility.

Consequently the algebraic coordinate sheaf map is the actual geometric
map into the closed-component pushforward. Its values on restrictions of
global sections retain the original component restrictions on every open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original tilde-unit comparison retains every original numerator,
on every open of the actual affine scheme. -/
theorem affineUnitIso_hom_toOpen (R : Type u) [CommRing R]
    (U : (Spec (CommRingCat.of R)).Opens) (r : R) :
    (AffineModuleTilde.unitIso R).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen (ModuleCat.of R R) U r) =
      StructureSheaf.toOpen R U r := by
  apply Subtype.ext
  funext p
  change AffineModuleTilde.unitFiberEquiv R p.val
      (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl R r) =
    algebraMap R (Localization.AtPrime p.val.asIdeal) r
  exact AffineModuleTilde.unitFiberEquiv_mkLinearMap R p.val r

variable (A : Type u) [CommRing A] (I : Ideal A)
  (L : InvertibleSheaf (Spec (CommRingCat.of A)))
  (frame : (schemeModulePullback (closedComponentInclusion A I)).obj L.obj ≅
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)

/-- The actual frame, transposed by the original scheme adjunction, gives
the geometric restriction-coordinate map into the original closed pushforward. -/
def closedComponentFrameSheafMap : L.obj ⟶ componentUnitPushforward A (A ⧸ I) :=
  (schemeModulePullbackPushforwardAdjunction (closedComponentInclusion A I)).homEquiv
    L.obj (_root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)
    frame.hom

/-- The previously extracted module frame gives exactly the original
geometric frame after the original counit and pullback comparisons. -/
theorem closedComponentFrameModuleIso_comparison :
    (AffineModuleTilde.pullbackIso (Ideal.Quotient.mk I)
        (AffineModuleTilde.sectionModule L.obj ⊤)).hom ≫
      AffineModuleTilde.map (closedComponentFrameModuleIso A I L frame).hom ≫
        (AffineModuleTilde.unitIso (A ⧸ I)).hom =
    (schemeModulePullback (closedComponentInclusion A I)).map
        (AffineModuleTilde.invertibleCounitIso L).hom ≫ frame.hom := by
  rw [closedComponentFrameModuleIso_map_hom]
  simp only [closedComponentFrameTildeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- On every original global section, the actual geometric frame map
has exactly the previously constructed original component coordinate. -/
theorem closedComponentFrameSheafMap_top
    (m : AffineModuleTilde.sectionModule L.obj ⊤) :
    (closedComponentFrameSheafMap A I L frame).val.app (op ⊤) m =
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv
        (closedComponentCoordinate A I L frame m) := by
  have h := AffineModuleTilde.pullbackIso_homEquiv_apply
    (Ideal.Quotient.mk I) (AffineModuleTilde.sectionModule L.obj ⊤)
    (_root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)
    (AffineModuleTilde.map (closedComponentFrameModuleIso A I L frame).hom ≫
      (AffineModuleTilde.unitIso (A ⧸ I)).hom) m
  rw [closedComponentFrameModuleIso_comparison,
    Adjunction.homEquiv_naturality_left] at h
  change (closedComponentFrameSheafMap A I L frame).val.app (op ⊤)
      ((AffineModuleTilde.invertibleCounitIso L).hom.val.app (op ⊤)
        (ModuleCat.Tilde.toOpen (AffineModuleTilde.sectionModule L.obj ⊤) ⊤ m)) =
    (AffineModuleTilde.unitIso (A ⧸ I)).hom.val.app (op ⊤)
      ((AffineModuleTilde.map (closedComponentFrameModuleIso A I L frame).hom).val.app
        (op ⊤) (ModuleCat.Tilde.toOpen
          ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj
            (AffineModuleTilde.sectionModule L.obj ⊤)) ⊤
          ((1 : A ⧸ I) ⊗ₜ[A, Ideal.Quotient.mk I] m))) at h
  rw [AffineModuleTilde.invertibleCounitIso_hom_toOpen,
    AffineModuleTilde.map_app_toOpen, affineUnitIso_hom_toOpen] at h
  have hid : L.obj.val.map (homOfLE (show (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ ⊤
      from le_top)).op m = m := by
    change L.obj.val.presheaf.map (𝟙 (op (⊤ : (Spec (CommRingCat.of A)).Opens))) m = m
    exact ConcreteCategory.congr_hom (L.obj.val.presheaf.map_id _) m
  rw [hid] at h
  exact h

/-- The same original coordinate equation holds on every open after
the actual restriction of the original global section. -/
theorem closedComponentFrameSheafMap_restrict_global
    (U : (Spec (CommRingCat.of A)).Opens)
    (m : AffineModuleTilde.sectionModule L.obj ⊤) :
    (closedComponentFrameSheafMap A I L frame).val.app (op U)
        (L.obj.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m) =
      (componentUnitPushforward A (A ⧸ I)).val.map
        (homOfLE (show U ≤ ⊤ from le_top)).op
        ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv
          (closedComponentCoordinate A I L frame m)) := by
  have h := ConcreteCategory.congr_hom
    ((closedComponentFrameSheafMap A I L frame).val.naturality
      (homOfLE (show U ≤ ⊤ from le_top)).op) m
  change (closedComponentFrameSheafMap A I L frame).val.app (op U)
      (L.obj.val.map (homOfLE (show U ≤ ⊤ from le_top)).op m) =
    (componentUnitPushforward A (A ⧸ I)).val.map
      (homOfLE (show U ≤ ⊤ from le_top)).op
      ((closedComponentFrameSheafMap A I L frame).val.app (op ⊤) m) at h
  rw [closedComponentFrameSheafMap_top] at h
  exact h

/-- The algebraic coordinate morphism used by the affine descent kernel
is the actual transpose of the given geometric component frame. -/
theorem closedComponentFrameSheafMap_eq :
    (closedComponentFrameSheafMap A I L frame) =
      (AffineModuleTilde.invertibleCounitIso L).inv ≫
        AffineModuleTilde.map (ModuleCat.ofHom
          (X := AffineModuleTilde.sectionModule L.obj ⊤) (Y := A ⧸ I)
          (closedComponentCoordinate A I L frame)) ≫
        (quotientTildePushforwardUnitIso A I).hom := by
  apply (cancel_epi (AffineModuleTilde.invertibleCounitIso L).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply AffineModuleTilde.tilde_hom_ext
  intro f m
  change (closedComponentFrameSheafMap A I L frame).val.app
      (op (PrimeSpectrum.basicOpen f))
      ((AffineModuleTilde.invertibleCounitIso L).hom.val.app
        (op (PrimeSpectrum.basicOpen f))
        (ModuleCat.Tilde.toOpen (AffineModuleTilde.sectionModule L.obj ⊤)
          (PrimeSpectrum.basicOpen f) m)) =
    (quotientTildePushforwardUnitIso A I).hom.val.app
      (op (PrimeSpectrum.basicOpen f))
      ((AffineModuleTilde.map (ModuleCat.ofHom
        (X := AffineModuleTilde.sectionModule L.obj ⊤) (Y := A ⧸ I)
        (closedComponentCoordinate A I L frame))).val.app
          (op (PrimeSpectrum.basicOpen f))
          (ModuleCat.Tilde.toOpen (AffineModuleTilde.sectionModule L.obj ⊤)
            (PrimeSpectrum.basicOpen f) m))
  rw [AffineModuleTilde.invertibleCounitIso_hom_toOpen,
    AffineModuleTilde.map_app_toOpen]
  exact (closedComponentFrameSheafMap_restrict_global A I L frame
    (PrimeSpectrum.basicOpen f) m).trans
      (componentUnitTildePushforwardIso_toOpen A (A ⧸ I)
        (PrimeSpectrum.basicOpen f) (closedComponentCoordinate A I L frame m)).symm

end KltDP.Geometry.RationalTreePicard
