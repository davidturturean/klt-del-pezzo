import KltDP.Geometry.AffineBlowupExceptionalIdealTildeComparison
import KltDP.Geometry.SchemeKernelFrameSquare

/-!
# The original exceptional kernel on a refined Rees chart

The ideal is the original center extended along the actual composite ring
map. The original Rees kernel frame pulls back to the same equation as the
native ideal frame. Their comparison therefore preserves the whole original
inclusion. Regularity of the image equation is the only refinement condition;
the application to principal localizations derives it from the Rees equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineBlowup

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable {B : Type u} [CommRing B] (θ : chartRing I a →+* B)

/-- The original center ideal extended along the actual refined chart map. -/
def refinedCenterIdeal : Ideal B := Ideal.map (θ.comp (chartBaseMap I a)) I

def refinedCenterEquation : refinedCenterIdeal I a θ :=
  ⟨θ (chartBaseMap I a (a : R)), Ideal.mem_map_of_mem (θ.comp (chartBaseMap I a)) a.property⟩

theorem span_refinedCenterEquation :
    Ideal.span {(refinedCenterEquation I a θ : B)} = refinedCenterIdeal I a θ := by
  change Ideal.span {θ (chartBaseMap I a (a : R))} =
    Ideal.map (θ.comp (chartBaseMap I a)) I
  rw [← Ideal.map_map, map_chartBaseMap_ideal, Ideal.map_span, Set.image_singleton]

/-- The same original Rees chart, preceded by the actual refinement map. -/
def refinedChartMap : Spec (CommRingCat.of B) ⟶ scheme I :=
  Spec.map (CommRingCat.ofHom θ) ≫ chartι I a

/-- Pull the original normalized kernel frame along that actual refinement. -/
def refinedKernelFrameIso :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf ≅
      (schemeModulePullback (refinedChartMap I a θ)).obj (exceptionalIdealModule I) :=
  (schemeModulePullbackUnitIso (Spec.map (CommRingCat.ofHom θ))).symm ≪≫
    (schemeModulePullback (Spec.map (CommRingCat.ofHom θ))).mapIso
      (originalChartKernelFrameIso I a) ≪≫
    (schemeModulePullbackCompIso (Spec.map (CommRingCat.ofHom θ)) (chartι I a)).app
      (exceptionalIdealModule I)

theorem refinedKernelFrameIso_inclusion :
    (refinedKernelFrameIso I a θ).hom ≫
      pulledKernelInclusion (exceptionalIdeal I).gluedTo (refinedChartMap I a θ) =
    schemeScalarEnd ((Scheme.ΓSpecIso (CommRingCat.of B)).inv
      (θ (chartBaseMap I a (a : R)))) := by
  simp only [refinedKernelFrameIso, refinedChartMap, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, exceptionalIdealModule, exceptionalι, Category.assoc]
  rw [schemeKernelPullbackCompIso_inclusion, ← Functor.map_comp_assoc,
    originalChartKernelFrameIso_inclusion, ← Category.assoc,
    schemeModulePullbackUnitIso_inv_scalar, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact congrArg schemeScalarEnd
    (AffineModuleTilde.specMap_globalScalar θ (chartBaseMap I a (a : R)))

variable (hregular : θ (chartBaseMap I a (a : R)) ∈ nonZeroDivisors B)

/-- The actual extended ideal is the original global exceptional kernel pullback. -/
def refinedIdealTildeGlobalIso :
    (ModuleCat.of B (refinedCenterIdeal I a θ)).tilde ≅
      (schemeModulePullback (refinedChartMap I a θ)).obj (exceptionalIdealModule I) :=
  (AffinePrincipalIdealTildeFrame.frameIso (refinedCenterIdeal I a θ)
    (refinedCenterEquation I a θ) (span_refinedCenterEquation I a θ) hregular).symm ≪≫
      refinedKernelFrameIso I a θ

/-- Both original whole inclusions agree under the actual ideal comparison. -/
theorem refinedIdealTildeGlobalIso_inclusion :
    (refinedIdealTildeGlobalIso I a θ hregular).hom ≫
      pulledKernelInclusion (exceptionalIdeal I).gluedTo (refinedChartMap I a θ) =
    AffinePrincipalIdealTildeFrame.inclusion (refinedCenterIdeal I a θ) := by
  rw [refinedIdealTildeGlobalIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    refinedKernelFrameIso_inclusion, Scheme.ΓSpecIso_inv]
  change (AffinePrincipalIdealTildeFrame.frameIso (refinedCenterIdeal I a θ)
      (refinedCenterEquation I a θ) (span_refinedCenterEquation I a θ) hregular).inv ≫
    schemeScalarEnd (Y := Spec (CommRingCat.of B))
      (StructureSheaf.toOpen B ⊤ (refinedCenterEquation I a θ : B)) = _
  rw [← AffinePrincipalIdealTildeFrame.frameIso_inclusion
    (refinedCenterIdeal I a θ) (refinedCenterEquation I a θ)
      (span_refinedCenterEquation I a θ) hregular, Iso.inv_hom_id_assoc]

end KltDP.Geometry.AffineBlowup
