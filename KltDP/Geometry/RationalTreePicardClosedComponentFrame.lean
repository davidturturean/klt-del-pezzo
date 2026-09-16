import KltDP.Geometry.RationalTreePicardClosedInvertibleDescent
import KltDP.Geometry.AffineModuleTildePullback

/-!
# Original closed-component frames give original tensor-module frames

An actual frame of the pullback of an invertible sheaf to Spec(A/I)
induces an isomorphism of the original scalar-extension module with A/I.
The construction uses the existing affine counit, actual pullback/tilde
comparison, and full faithfulness of tilde. Its image under tilde is the
original geometric composite, so the component frame is not replaced
by an unrelated module basis.

The input is an actual geometric component trivialization. Producing
these frames from zero degree on the original projective-line components,
and comparing their two original fibers at a node, remain necessary.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (A : Type u) [CommRing A] (I : Ideal A)
  (L : InvertibleSheaf (Spec (CommRingCat.of A)))

/-- The actual original inclusion of the closed component. -/
abbrev closedComponentInclusion :
    Spec (CommRingCat.of (A ⧸ I)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

variable (frame : (schemeModulePullback (closedComponentInclusion A I)).obj L.obj ≅
  _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ I))).ringCatSheaf)

/-- Re-express the given geometric frame through the original affine
pullback and counit comparisons. -/
def closedComponentFrameTildeIso :
    ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj
      (AffineModuleTilde.sectionModule L.obj ⊤)).tilde ≅
      (ModuleCat.of (A ⧸ I) (A ⧸ I)).tilde :=
  (AffineModuleTilde.pullbackIso (Ideal.Quotient.mk I)
    (AffineModuleTilde.sectionModule L.obj ⊤)).symm ≪≫
      (schemeModulePullback (closedComponentInclusion A I)).mapIso
        (AffineModuleTilde.invertibleCounitIso L) ≪≫
          frame ≪≫ (AffineModuleTilde.unitIso (A ⧸ I)).symm

/-- Full faithfulness yields a frame of the original tensor-extension
module from the actual geometric component frame. -/
def closedComponentFrameModuleIso :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj
      (AffineModuleTilde.sectionModule L.obj ⊤) ≅ ModuleCat.of (A ⧸ I) (A ⧸ I) :=
  (AffineModuleTilde.fullyFaithfulFunctor (A ⧸ I)).preimageIso
    (closedComponentFrameTildeIso A I L frame)

/-- The induced module frame reproduces exactly the original geometric
frame composite when passed back to the actual tilde sheaves. -/
theorem closedComponentFrameModuleIso_map_hom :
    AffineModuleTilde.map (closedComponentFrameModuleIso A I L frame).hom =
      (closedComponentFrameTildeIso A I L frame).hom := by
  exact (AffineModuleTilde.fullyFaithfulFunctor (A ⧸ I)).map_preimage _

end KltDP.Geometry.RationalTreePicard
