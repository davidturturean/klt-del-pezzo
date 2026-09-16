import KltDP.Geometry.CartierPullbackFrameSquare
import KltDP.Geometry.SchemeKernelFrameSquare

/-!
# The two frames of a Cartier pullback on a compatible chart pair

Third module of the general Cartier comparison `π^* I_D ≅ I_{π^*D}`, for a generic-point-preserving
morphism `π : X ⟶ Y` of integral schemes and an effective Cartier divisor `D` on `Y` with regular
equations.

On a compatible chart pair — a regular chart `(U, f, c)` of `D`, an affine `V ≤ U` of `Y` and an
affine `W ≤ π ⁻¹ᵁ V` of `X` — both modules are framed on `W` by multiplication by the *same*
section:

* `targetFrame` trivialises `I_{π^*D}` on `W` (accepted `gluedAffineKernelIso`, whose hypotheses are
  the compiled `pullbackIdeal_eq_span` and `pullbackCoefficient_regular`), normalised through
  `localKernelToGlobalPullbackIso`; its inclusion is multiplication by the transported
  `π.appLE U W c` (`targetFrame_inclusion`);
* `sourceFrame` trivialises `I_D` on `V` the same way, and `pulledSourceFrame` transports it to `W`
  along the chart square with the accepted `schemeKernelFrameOnSquare`; its inclusion is
  multiplication by the transported `chartMap.appTop` of the equation of `V`, which is the same
  section by `chartMap_appTop` together with the compiled `appLE_restrict_eq`.

Because the two inclusions are **equal**, `pulledSourceFrame.symm ≪≫ targetFrame` is compatible with
the inclusions into the structure module with no monicity argument (`chartComparisonIso_map`), which
is exactly the input the accepted `schemeModuleMonicFactorIsoOnOpenCover` consumes.

Nothing here assumes flatness of `π`, nor that `π` is open or an isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierPullbackChartFrames

open KltDP.Geometry KltDP.Geometry.CartierPullbackFrameCharts
  KltDP.Geometry.CartierPullbackFrameSquare

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Cancel a common final isomorphism (the accepted private lemma, restated). -/
private theorem cancel_final_iso' {C : Type*} [Category C]
    {M N Q R : C} (e : Q ≅ R) (a : M ⟶ N) (b : N ⟶ Q) (c : M ⟶ Q)
    (h : a ≫ b ≫ e.hom = c ≫ e.hom) : a ≫ b = c := by
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc] using h

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y)
  [GenericPointPreserving π] (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)

/-! ### The frame of `I_D` on a chart of `Y` -/

/-- The trivialisation of the ideal sheaf of `D` on an affine open `V` inside a regular chart,
normalised as a frame of the pullback of the global kernel module along `V.ι`. -/
def sourceFrame (c : RegularCartierEquationChart Y D) (V : Y.affineOpens) [Nonempty V.1]
    (hV : V.1 ≤ c.chart.openSet) :
    _root_.SheafOfModules.unit V.1.toScheme.ringCatSheaf ≅
      (schemeModulePullback V.1.ι).obj
        (schemeKernelIdeal (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo) :=
  gluedAffineKernelIso (effectiveCartierIdealDataOfRegularEquations Y D hD) V
      (chartCoefficient D c V hV) (chartIdeal_eq_span D hD c V hV)
      (chartCoefficient_regular D c V hV) ≪≫
    localKernelToGlobalPullbackIso
      (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo V.1

set_option maxHeartbeats 4000000 in
/-- That frame is multiplication by the transported restricted coefficient. -/
theorem sourceFrame_inclusion (c : RegularCartierEquationChart Y D) (V : Y.affineOpens)
    [Nonempty V.1] (hV : V.1 ≤ c.chart.openSet) :
    (sourceFrame D hD c V hV).hom ≫
        pulledKernelInclusion
          (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo V.1.ι =
      schemeScalarEnd (gluedAffineEquation V (chartCoefficient D c V hV)) := by
  change (schemeKernelGenerator
        ((effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo ∣_ V.1)
        (gluedAffineEquation V (chartCoefficient D c V hV))
        (gluedAffineEquation_eq_zero (effectiveCartierIdealDataOfRegularEquations Y D hD) V
          (chartCoefficient D c V hV) (chartIdeal_eq_span D hD c V hV)) ≫
      (localKernelToGlobalPullbackIso
        (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo V.1).hom) ≫
        pulledKernelInclusion
          (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo V.1.ι = _
  rw [Category.assoc, localKernelToGlobalPullbackIso_inclusion, schemeKernelGenerator_comp_ι]

/-! ### The frame of `I_{π^*D}` on a chart of `X` -/

/-- The trivialisation of the ideal sheaf of `π^*D` on an affine open `W` inside the preimage of a
regular chart, normalised as a frame of the pullback of the global kernel module along `W.ι`. -/
def targetFrame (c : RegularCartierEquationChart Y D) (W : X.affineOpens) [Nonempty W.1]
    (hWc : W.1 ≤ π ⁻¹ᵁ c.chart.openSet) :
    _root_.SheafOfModules.unit W.1.toScheme.ringCatSheaf ≅
      (schemeModulePullback W.1.ι).obj
        (schemeKernelIdeal (pullbackIdealData π D hD).gluedTo) :=
  gluedAffineKernelIso (pullbackIdealData π D hD) W
      (π.appLE c.chart.openSet W.1 hWc c.coefficient)
      (pullbackIdeal_eq_span π D hD c W hWc)
      (pullbackCoefficient_regular π D c W hWc) ≪≫
    localKernelToGlobalPullbackIso (pullbackIdealData π D hD).gluedTo W.1

set_option maxHeartbeats 4000000 in
/-- That frame is multiplication by the transported pulled-back coefficient. -/
theorem targetFrame_inclusion (c : RegularCartierEquationChart Y D) (W : X.affineOpens)
    [Nonempty W.1] (hWc : W.1 ≤ π ⁻¹ᵁ c.chart.openSet) :
    (targetFrame π D hD c W hWc).hom ≫
        pulledKernelInclusion (pullbackIdealData π D hD).gluedTo W.1.ι =
      schemeScalarEnd
        (gluedAffineEquation W (π.appLE c.chart.openSet W.1 hWc c.coefficient)) := by
  change (schemeKernelGenerator ((pullbackIdealData π D hD).gluedTo ∣_ W.1)
        (gluedAffineEquation W (π.appLE c.chart.openSet W.1 hWc c.coefficient))
        (gluedAffineEquation_eq_zero (pullbackIdealData π D hD) W
          (π.appLE c.chart.openSet W.1 hWc c.coefficient)
          (pullbackIdeal_eq_span π D hD c W hWc)) ≫
      (localKernelToGlobalPullbackIso (pullbackIdealData π D hD).gluedTo W.1).hom) ≫
        pulledKernelInclusion (pullbackIdealData π D hD).gluedTo W.1.ι = _
  rw [Category.assoc, localKernelToGlobalPullbackIso_inclusion, schemeKernelGenerator_comp_ι]

/-! ### Transport of the `Y`-frame across the chart square -/

/-- The frame of `I_D` on `V`, transported to `W` along the chart square. -/
def pulledSourceFrame (c : RegularCartierEquationChart Y D) (V : Y.affineOpens) [Nonempty V.1]
    (hV : V.1 ≤ c.chart.openSet) (W : X.affineOpens) (hW : W.1 ≤ π ⁻¹ᵁ V.1) :
    _root_.SheafOfModules.unit W.1.toScheme.ringCatSheaf ≅
      (schemeModulePullback W.1.ι).obj
        ((schemeModulePullback π).obj
          (schemeKernelIdeal (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo)) :=
  schemeKernelFrameOnSquare
    (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo V.1.ι
    (chartMap π V W hW) W.1.ι π (chartMap_ι π V W hW) (sourceFrame D hD c V hV)

set_option maxHeartbeats 4000000 in
/-- The transported frame is multiplication by the pulled-back restricted coefficient. -/
theorem pulledSourceFrame_inclusion (c : RegularCartierEquationChart Y D) (V : Y.affineOpens)
    [Nonempty V.1] (hV : V.1 ≤ c.chart.openSet) (W : X.affineOpens) (hW : W.1 ≤ π ⁻¹ᵁ V.1) :
    (pulledSourceFrame π D hD c V hV W hW).hom ≫
        (schemeModulePullback W.1.ι).map
          (pulledKernelInclusion
            (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo π) ≫
        (schemeModulePullbackUnitIso W.1.ι).hom =
      schemeScalarEnd
        (gluedAffineEquation W (π.appLE V.1 W.1 hW (chartCoefficient D c V hV))) := by
  have h := schemeKernelFrameOnSquare_inclusion
    (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo V.1.ι
    (chartMap π V W hW) W.1.ι π (chartMap_ι π V W hW) (sourceFrame D hD c V hV)
    (gluedAffineEquation V (chartCoefficient D c V hV))
    (sourceFrame_inclusion D hD c V hV)
  rw [chartMap_appTop] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- The same, written with the coefficient of the regular chart itself. -/
theorem pulledSourceFrame_inclusion' (c : RegularCartierEquationChart Y D) (V : Y.affineOpens)
    [Nonempty V.1] (hV : V.1 ≤ c.chart.openSet) (W : X.affineOpens) (hW : W.1 ≤ π ⁻¹ᵁ V.1)
    (hWc : W.1 ≤ π ⁻¹ᵁ c.chart.openSet) :
    (pulledSourceFrame π D hD c V hV W hW).hom ≫
        (schemeModulePullback W.1.ι).map
          (pulledKernelInclusion
            (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo π) ≫
        (schemeModulePullbackUnitIso W.1.ι).hom =
      schemeScalarEnd
        (gluedAffineEquation W (π.appLE c.chart.openSet W.1 hWc c.coefficient)) := by
  rw [← appLE_restrict_eq π D c V hV W hW hWc]
  exact pulledSourceFrame_inclusion π D hD c V hV W hW

/-! ### The comparison on one chart pair -/

/-- **On a compatible chart pair the two ideal modules agree.** -/
def chartComparisonIso (c : RegularCartierEquationChart Y D) (V : Y.affineOpens) [Nonempty V.1]
    (hV : V.1 ≤ c.chart.openSet) (W : X.affineOpens) [Nonempty W.1] (hW : W.1 ≤ π ⁻¹ᵁ V.1)
    (hWc : W.1 ≤ π ⁻¹ᵁ c.chart.openSet) :
    (schemeModulePullback W.1.ι).obj
        ((schemeModulePullback π).obj
          (schemeKernelIdeal (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo)) ≅
      (schemeModulePullback W.1.ι).obj
        (schemeKernelIdeal (pullbackIdealData π D hD).gluedTo) :=
  (pulledSourceFrame π D hD c V hV W hW).symm ≪≫ targetFrame π D hD c W hWc

set_option maxHeartbeats 4000000 in
/-- **The comparison is compatible with the inclusions into the structure module.** -/
theorem chartComparisonIso_map (c : RegularCartierEquationChart Y D) (V : Y.affineOpens)
    [Nonempty V.1] (hV : V.1 ≤ c.chart.openSet) (W : X.affineOpens) [Nonempty W.1]
    (hW : W.1 ≤ π ⁻¹ᵁ V.1) (hWc : W.1 ≤ π ⁻¹ᵁ c.chart.openSet) :
    (chartComparisonIso π D hD c V hV W hW hWc).hom ≫
        (schemeModulePullback W.1.ι).map
          (schemeKernelIdealι (pullbackIdealData π D hD).gluedTo) =
      (schemeModulePullback W.1.ι).map
        (pulledKernelInclusion
          (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo π) := by
  have h1 := pulledSourceFrame_inclusion' π D hD c V hV W hW hWc
  have h2 := targetFrame_inclusion π D hD c W hWc
  have h3 : (chartComparisonIso π D hD c V hV W hW hWc).hom ≫
      pulledKernelInclusion (pullbackIdealData π D hD).gluedTo W.1.ι =
        (schemeModulePullback W.1.ι).map
          (pulledKernelInclusion
            (effectiveCartierIdealDataOfRegularEquations Y D hD).gluedTo π) ≫
          (schemeModulePullbackUnitIso W.1.ι).hom := by
    rw [chartComparisonIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, h2]
    exact ((Iso.eq_inv_comp _).mpr h1).symm
  rw [pulledKernelInclusion] at h3
  exact cancel_final_iso' _ _ _ _ h3

end KltDP.Geometry.CartierPullbackChartFrames
