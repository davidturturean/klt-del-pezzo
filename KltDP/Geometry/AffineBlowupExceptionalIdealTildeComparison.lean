import KltDP.Geometry.AffineBlowupExceptionalKernelChartFrame
import KltDP.Geometry.AffinePrincipalIdealTildeFrame

/-!
# The original Rees ideal tilde is the actual global exceptional kernel pullback

The native extended center ideal and the restriction of the original global
exceptional kernel have frames defined by the same original Rees equation.
Their comparison therefore preserves the original inclusions into the chart
structure module. No ideal comparison or frame compatibility is a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineBlowup

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)

/-- The native extended center ideal on the original affine Rees chart. -/
abbrev chartIdealModule : ModuleCat.{u} (chartRing I a) :=
  ModuleCat.of (chartRing I a) (chartCenterIdeal I a)

/-- Its original tilde inclusion into the actual chart structure module. -/
def chartIdealTildeInclusion : (chartIdealModule I a).tilde ⟶
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (chartRing I a))).ringCatSheaf :=
  AffinePrincipalIdealTildeFrame.inclusion (chartCenterIdeal I a)

/-- The proved original regular Rees equation supplies the native ideal frame. -/
def chartIdealTildeFrameIso :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (chartRing I a))).ringCatSheaf ≅
      (chartIdealModule I a).tilde :=
  AffinePrincipalIdealTildeFrame.frameIso (chartCenterIdeal I a) (chartCenterEquation I a)
    (span_chartCenterEquation I a) (chartCenterEquation_regular I a)

theorem chartIdealTildeFrameIso_inclusion :
    (chartIdealTildeFrameIso I a).hom ≫ chartIdealTildeInclusion I a =
      schemeScalarEnd (Y := Spec (CommRingCat.of (chartRing I a)))
        (StructureSheaf.toOpen (chartRing I a) ⊤ (chartCenterEquation I a)) :=
  AffinePrincipalIdealTildeFrame.frameIso_inclusion (chartCenterIdeal I a)
    (chartCenterEquation I a) (span_chartCenterEquation I a) (chartCenterEquation_regular I a)

/-- The actual ideal tilde and the pullback of the actual global kernel are identified. -/
def originalChartIdealTildeGlobalIso :
    (chartIdealModule I a).tilde ≅
      (schemeModulePullback (chartι I a)).obj (exceptionalIdealModule I) :=
  (chartIdealTildeFrameIso I a).symm ≪≫ originalChartKernelFrameIso I a

/-- This actual isomorphism retains the original whole ideal inclusion. -/
theorem originalChartIdealTildeGlobalIso_inclusion :
    (originalChartIdealTildeGlobalIso I a).hom ≫
        pulledKernelInclusion (exceptionalIdeal I).gluedTo (chartι I a) =
      chartIdealTildeInclusion I a := by
  change ((chartIdealTildeFrameIso I a).inv ≫ (originalChartKernelFrameIso I a).hom) ≫
    pulledKernelInclusion (exceptionalIdeal I).gluedTo (chartι I a) = _
  rw [Category.assoc, originalChartKernelFrameIso_inclusion, Scheme.ΓSpecIso_inv]
  change (chartIdealTildeFrameIso I a).inv ≫
      schemeScalarEnd (Y := Spec (CommRingCat.of (chartRing I a)))
        (StructureSheaf.toOpen (chartRing I a) ⊤ (chartCenterEquation I a)) = _
  rw [← chartIdealTildeFrameIso_inclusion I a, Iso.inv_hom_id_assoc]

end KltDP.Geometry.AffineBlowup
