import KltDP.Geometry.GluedIdealKernelTrivialization
import KltDP.Geometry.SchemeKernelRestriction
import KltDP.Geometry.AffineModuleTildeFunctor
import KltDP.Geometry.AffineModuleTildeUnit
import KltDP.RingTheory.RegularPrincipalConormal

/-!
# Actual quotient-chart coordinates for the global conormal sheaf

On an actual affine chart where an ideal sheaf has a regular principal
equation, the original tilde sheaf of the actual module I/I² is isomorphic
to the restriction of the global conormal sheaf to the actual quotient
chart. Both sides have constructed equation frames. The isomorphism
identifies those frames, with an equality on every open of the chart.

This uses the actual kernel restriction comparison, the actual scheme
chart isomorphism, and functoriality of the pinned tilde construction.
It does not assume affine reconstruction, an abstract conormal-sheaf
identification, or invertibility. Compatibility between different chart
equations and identification with a projective O(1) remain separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace AffineModuleTilde

/-- The actual tilde-unit comparison sends the original constant section
of 1 to the original unit section on every open. -/
theorem unitIso_hom_toOpen_one (R : Type u) [CommRing R]
    (V : (Spec (CommRingCat.of R)).Opens) :
    (unitIso R).hom.val.app (op V)
        (ModuleCat.Tilde.toOpen (ModuleCat.of R R) V (1 : R)) =
      (1 : Γ(Spec (CommRingCat.of R), V)) := by
  apply Subtype.ext
  funext p
  change unitFiberEquiv R p.val
      (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl R (1 : R)) =
    (1 : Localization.AtPrime p.val.asIdeal)
  rw [unitFiberEquiv_mkLinearMap, (algebraMap R (Localization.AtPrime p.val.asIdeal)).map_one]

end AffineModuleTilde

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- The actual global conormal restricted first to the inverse-image
open and then along the original quotient-chart isomorphism. -/
def gluedAffineGlobalConormal : (I.glueDataObj U).Modules :=
  (SchemeModuleRestriction.restriction (I.glueDataObjIso U).hom).obj
    ((SchemeModuleRestriction.restriction (I.gluedTo ⁻¹ᵁ U.1).ι).obj
      (schemeConormalSheaf I.gluedTo))

variable (d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
  (hregular : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The defining equation as an element of the actual affine ideal. -/
def gluedAffineIdealEquation : I.ideal U :=
  ⟨d, hI.symm ▸ Ideal.subset_span (Set.mem_singleton d)⟩

/-- The actual quotient-module coordinates send 1 to the class of the
chosen regular equation in the actual conormal module. -/
def gluedAffineCotangentEquiv :
    (Γ(X, U.1) ⧸ I.ideal U) ≃ₗ[Γ(X, U.1) ⧸ I.ideal U] (I.ideal U).Cotangent :=
  KltDP.RingTheory.principalConormalEquiv (I.ideal U)
    (gluedAffineIdealEquation I U d hI) hI.symm hregular

@[simp]
theorem gluedAffineCotangentEquiv_one :
    gluedAffineCotangentEquiv I U d hI hregular 1 =
      (I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI) :=
  KltDP.RingTheory.principalConormalEquiv_one (I.ideal U)
    (gluedAffineIdealEquation I U d hI) hI.symm hregular

/-- The unit frame is obtained from the original multiplication map
into the kernel, its actual pullback, and the actual restriction isomorphism. -/
def gluedAffineGlobalConormalUnitIso :
    _root_.SheafOfModules.unit (I.glueDataObj U).ringCatSheaf ≅
      gluedAffineGlobalConormal I U :=
  (SchemeModuleRestriction.restrictionUnitIso (I.glueDataObjIso U).hom).symm ≪≫
    (SchemeModuleRestriction.restriction (I.glueDataObjIso U).hom).mapIso
      (gluedAffineConormalIso I U d hI hregular ≪≫
        (schemeConormalRestrictionIso I.gluedTo U.1).symm)

/-- Tilde of the actual conormal module is the actual global conormal
on its quotient chart, through the two constructed equation frames. -/
def gluedAffineConormalTildeIso :
    (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent).tilde ≅
      gluedAffineGlobalConormal I U :=
  (AffineModuleTilde.linearEquivIso
    (M := ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (Γ(X, U.1) ⧸ I.ideal U))
    (N := ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
    (gluedAffineCotangentEquiv I U d hI hregular)).symm ≪≫
      AffineModuleTilde.unitIso (Γ(X, U.1) ⧸ I.ideal U) ≪≫
        gluedAffineGlobalConormalUnitIso I U d hI hregular

/-- The full sheaf comparison preserves the chosen actual equation
frame, already as an equality of module-sheaf morphisms. -/
theorem gluedAffineConormalTildeIso_frame :
    (AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (Γ(X, U.1) ⧸ I.ideal U))
      (N := ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent)
      (gluedAffineCotangentEquiv I U d hI hregular)).hom ≫
        (gluedAffineConormalTildeIso I U d hI hregular).hom =
      (AffineModuleTilde.unitIso (Γ(X, U.1) ⧸ I.ideal U)).hom ≫
        (gluedAffineGlobalConormalUnitIso I U d hI hregular).hom := by
  simp only [gluedAffineConormalTildeIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]

/-- On every actual chart open, the original section of the defining
equation class maps to the frame constructed from the actual kernel map. -/
theorem gluedAffineConormalTildeIso_toOpen_equation (V : (I.glueDataObj U).Opens) :
    (gluedAffineConormalTildeIso I U d hI hregular).hom.val.app (op V)
        (ModuleCat.Tilde.toOpen
          (ModuleCat.of (Γ(X, U.1) ⧸ I.ideal U) (I.ideal U).Cotangent) V
          ((I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI))) =
      (gluedAffineGlobalConormalUnitIso I U d hI hregular).hom.val.app (op V)
        (1 : Γ(I.glueDataObj U, V)) := by
  let B := Γ(X, U.1) ⧸ I.ideal U
  let E := gluedAffineCotangentEquiv I U d hI hregular
  have hmap := AffineModuleTilde.map_app_toOpen
    (M := ModuleCat.of B B) (N := ModuleCat.of B (I.ideal U).Cotangent)
    E.toModuleIso.hom V (1 : B)
  change (AffineModuleTilde.linearEquivIso
      (M := ModuleCat.of B B) (N := ModuleCat.of B (I.ideal U).Cotangent) E).hom.val.app
      (op V) (ModuleCat.Tilde.toOpen (ModuleCat.of B B) V (1 : B)) =
    ModuleCat.Tilde.toOpen (ModuleCat.of B (I.ideal U).Cotangent) V (E 1) at hmap
  have hE : E 1 = (I.ideal U).toCotangent (gluedAffineIdealEquation I U d hI) :=
    gluedAffineCotangentEquiv_one I U d hI hregular
  rw [hE] at hmap
  have h := congrArg
    (fun f => f.val.app (op V)
      (ModuleCat.Tilde.toOpen (ModuleCat.of B B) V (1 : B)))
    (gluedAffineConormalTildeIso_frame I U d hI hregular)
  change (gluedAffineConormalTildeIso I U d hI hregular).hom.val.app (op V)
      ((AffineModuleTilde.linearEquivIso
        (M := ModuleCat.of B B) (N := ModuleCat.of B (I.ideal U).Cotangent) E).hom.val.app
        (op V) (ModuleCat.Tilde.toOpen (ModuleCat.of B B) V (1 : B))) =
    (gluedAffineGlobalConormalUnitIso I U d hI hregular).hom.val.app (op V)
      ((AffineModuleTilde.unitIso B).hom.val.app (op V)
        (ModuleCat.Tilde.toOpen (ModuleCat.of B B) V (1 : B))) at h
  have hleft := congrArg
    (fun s => (gluedAffineConormalTildeIso I U d hI hregular).hom.val.app (op V) s)
    hmap.symm
  have hright := congrArg
    (fun s => (gluedAffineGlobalConormalUnitIso I U d hI hregular).hom.val.app (op V) s)
    (AffineModuleTilde.unitIso_hom_toOpen_one B V)
  exact hleft.trans (h.trans hright)

end KltDP.Geometry
