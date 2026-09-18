import KltDP.Geometry.PushforwardIntegralClosureDiagram

/-!
# Original integral-closure spectra and their canonical comparison

The original inclusion of integral elements induces the comparison of
the two actual spectrum diagrams. It commutes with every original base
map. For universally closed maps this is an isomorphism, so for qcqs
universally closed maps the original normalization charts satisfy the
same cartesian transition condition as the pushforward-section charts.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u

namespace KltDP.Geometry.IntegralClosureSpectrumDiagram

open Scheme.AffineZariskiSite PushforwardIntegralClosureDiagram
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original structure-sheaf map to the actual affine integral closure. -/
def affineScalarMap : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ affineDiagram f :=
  whiskerLeft (toOpensFunctor Y).op (scalarMap f)

/-- Its composition with the literal inclusion is the original pushforward scalar map. -/
theorem affineScalarMap_inclusion :
    affineScalarMap f ≫ affineInclusion f = PushforwardAffineDiagram.scalarMap f := by
  ext U x
  rfl

/-- Spectra of the original integral-closure rings and restrictions. -/
def spectra : Y.AffineZariskiSite ⥤ Scheme.{u} :=
  (affineDiagram f).rightOp ⋙ Scheme.Spec

/-- The original maps from these spectra to the original affine base spectra. -/
def toBaseSpectra : spectra f ⟶ toOpensFunctor Y ⋙ Y.presheaf.rightOp ⋙ Scheme.Spec :=
  whiskerRight (NatTrans.rightOp (affineScalarMap f)) Scheme.Spec

/-- The comparison induced by the literal inclusion of integral elements. -/
def comparisonHom : PushforwardAffineDiagram.spectra f ⟶ spectra f :=
  whiskerRight (NatTrans.rightOp (affineInclusion f)) Scheme.Spec

/-- Every comparison component is induced by an isomorphism of original section rings. -/
instance comparisonHom_isIso [UniversallyClosed f] : IsIso (comparisonHom f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  change IsIso (Spec.map ((affineInclusion f).app (op U)))
  infer_instance

/-- The actual two spectrum diagrams are canonically isomorphic. -/
def comparison [UniversallyClosed f] : PushforwardAffineDiagram.spectra f ≅ spectra f :=
  asIso (comparisonHom f)

/-- This comparison retains exactly the original scalar maps to the affine base. -/
theorem comparisonHom_toBase :
    comparisonHom f ≫ toBaseSpectra f = PushforwardAffineDiagram.toBaseSpectra f := by
  apply NatTrans.ext
  funext U
  change Spec.map ((affineInclusion f).app (op U)) ≫
    Spec.map ((affineScalarMap f).app (op U)) = Spec.map (f.app U.1)
  rw [← Spec.map_comp]
  rfl

/-- The actual integral-closure diagram has cartesian transitions over its original base. -/
theorem toBaseSpectra_equifibered [QuasiCompact f] [QuasiSeparated f]
    [UniversallyClosed f] : NatTrans.Equifibered (toBaseSpectra f) := by
  have h : toBaseSpectra f = (comparison f).inv ≫
      PushforwardAffineDiagram.toBaseSpectra f := by
    rw [← comparisonHom_toBase f]
    exact ((comparison f).inv_hom_id_assoc (toBaseSpectra f)).symm
  rw [h]
  exact (NatTrans.equifibered_of_isIso (comparison f).inv).comp
    (PushforwardAffineDiagram.toBaseSpectra_equifibered f)

end KltDP.Geometry.IntegralClosureSpectrumDiagram
