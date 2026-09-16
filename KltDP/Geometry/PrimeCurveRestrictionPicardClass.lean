import KltDP.Geometry.PrimeCurveCartierRestriction
import KltDP.Geometry.SchemeModulePullbackRestrict
import KltDP.Geometry.ModuleOpenOverEquivalence
import KltDP.Geometry.TransitionUnitPicardComparison
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# Picard classes of `i^*O_X(D)` and `O_C(D|_C)` from transition cocycles

The accepted trivializations of `O_X(D)` live on the over-sites of the equation
charts (`cartierEquationOverIso`). Through the accepted equivalence between
over-site modules and modules on the open subscheme (`openToOverEquivalence`) they
become scheme-level trivializations `restriction U.ι O_X(D) ≅ unit`, which pull back
along any morphism `f : Y ⟶ X` to trivializations of `f^*O_X(D)` on the preimage charts
(`schemeModulePullbackTrivialization`), and return to the over-site language by
`localTrivializationsOfOpenCharts`. This gives an explicit covering atlas of
`i^*O_X(D)` on the preimages `i⁻¹U_c` of the generic charts of a prime curve
`i : C → X`, indexed exactly like the restricted charts of `D|_C`.

Any covering atlas of an invertible sheaf identifies its Picard class with the class
of the cocycle extracted from that atlas (`recoveryIso`). Hence both
`[i^*O_X(D)]` and `[O_C(D|_C)]` are Picard classes of cocycles on the same cover
`(i⁻¹U_c)_c`, and their equality follows from a gauge equivalence of the two
extracted cocycles (`picardClass_eq_of_gauge`). The computation of the pulled-back
cocycle as the image `i.app g` of the surface cocycle is not carried out here; see
`F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section ChartTrivializations

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)

/-- The scheme-level unit trivialization of `O(D)` on an equation chart, obtained from the
accepted over-site trivialization through the open-subscheme/over-site equivalence. -/
def cartierChartRestrictionUnitIso (c : CartierEquationChart X D) :
    _root_.SheafOfModules.unit c.openSet.toScheme.ringCatSheaf ≅
      (SchemeModuleRestriction.restriction c.openSet.ι).obj (cartierDivisorModule X D) :=
  (openToOverFunctor c.openSet).preimageIso
    ((openToOverUnitIso c.openSet).symm ≪≫
      cartierEquationOverIso X D c.openSet c.equation c.represents ≪≫
      (openToOverRestrictionIso c.openSet (cartierDivisorModule X D)).symm)

/-- The same trivialization in the pullback language. -/
def cartierChartPullbackUnitIso (c : CartierEquationChart X D) :
    (schemeModulePullback c.openSet.ι).obj (cartierDivisorModule X D) ≅
      _root_.SheafOfModules.unit c.openSet.toScheme.ringCatSheaf :=
  ((SchemeModuleRestriction.restrictionIsoPullback c.openSet.ι).app
      (cartierDivisorModule X D)).symm ≪≫
    (cartierChartRestrictionUnitIso X D c).symm

variable {Y : Scheme.{u}} (f : Y ⟶ X)

/-- The pulled-back trivialization of `f^*O(D)` on the preimage of an equation chart. -/
def pullbackCartierChartUnitIso (c : CartierEquationChart X D) :
    _root_.SheafOfModules.unit (f ⁻¹ᵁ c.openSet).toScheme.ringCatSheaf ≅
      (SchemeModuleRestriction.restriction (f ⁻¹ᵁ c.openSet).ι).obj
        ((schemeModulePullback f).obj (cartierDivisorModule X D)) :=
  ((SchemeModuleRestriction.restrictionIsoPullback (f ⁻¹ᵁ c.openSet).ι).app
      ((schemeModulePullback f).obj (cartierDivisorModule X D)) ≪≫
    schemeModulePullbackTrivialization f c.openSet (cartierDivisorModule X D)
      (cartierChartPullbackUnitIso X D c)).symm

end ChartTrivializations

section PicardClassOfAtlas

variable (X : Scheme.{u})

/-- The Picard class of an invertible sheaf is the class of the cocycle extracted from any
covering atlas of unit trivializations. -/
theorem InvertibleSheaf.toPic_eq_picardClass (L : InvertibleSheaf X)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj)
    (hU : (⨆ i, t.X i) = ⊤) :
    L.toPic = TransitionUnitGluing.picardClass X t.X
      (TransitionUnitExtraction.transitionUnits X L.obj t)
      (TransitionUnitExtraction.transitionUnits_isCocycle X L.obj t) hU := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  rw [TransitionUnitGluing.picardClass_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨TransitionUnitExtraction.recoveryIso X L.obj t⟩

end PicardClassOfAtlas

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)

/-- The preimages of the generic charts cover the curve. -/
theorem iSup_chartPreimage_eq_top (hD : HasRegularCartierEquations X.toScheme D) :
    (⨆ c : C.GenericChart D, C.chartPreimage D c.1) = ⊤ := by
  apply eq_top_iff.mpr
  intro y _
  exact Opens.mem_iSup.mpr (C.exists_genericChart D hD y)

/-- The covering atlas of `i^*O_X(D)` on the preimages of the generic charts. -/
def pullbackLocalTrivializations :
    KltDP.SheafOfModules.LocalTrivializations (R := C.toScheme.ringCatSheaf)
      ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) :=
  localTrivializationsOfOpenCharts
    ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))
    (fun c : C.GenericChart D => C.chartPreimage D c.1)
    (fun y => C.exists_genericChart D hD y)
    (fun c => pullbackCartierChartUnitIso X.toScheme D C.inclusion c.1.chart)

/-- `[i^*O_X(D)]` is the Picard class of the cocycle extracted from the pulled-back atlas. -/
theorem pullback_toPic_eq_picardClass :
    (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D)).toPic =
      picardClass C.toScheme (fun c : C.GenericChart D => C.chartPreimage D c.1)
        (transitionUnits C.toScheme _ (C.pullbackLocalTrivializations D hD))
        (transitionUnits_isCocycle C.toScheme _ (C.pullbackLocalTrivializations D hD))
        (C.iSup_chartPreimage_eq_top D hD) :=
  InvertibleSheaf.toPic_eq_picardClass C.toScheme
    (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D))
    (C.pullbackLocalTrivializations D hD) (C.iSup_chartPreimage_eq_top D hD)

variable (hC : C.NotInSupport D hD)

/-- The covering atlas of `O_C(D|_C)` by the accepted trivializations on the restricted
charts. -/
def restrictedLocalTrivializations :
    KltDP.SheafOfModules.LocalTrivializations (R := C.toScheme.ringCatSheaf)
      (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)) where
  I := C.GenericChart D
  X c := C.chartPreimage D c.1
  coversTop := by
    intro W y hy
    obtain ⟨c, hc⟩ := C.exists_genericChart D hD y
    exact ⟨W ⊓ C.chartPreimage D c.1, homOfLE inf_le_left,
      ⟨c, ⟨homOfLE inf_le_right⟩⟩, ⟨hy, hc⟩⟩
  iso c := _root_.SheafOfModules.freeUniqueIsoUnit
      (R := C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) PUnit ≪≫
    cartierEquationOverIso C.toScheme (C.restrictCartier D hD hC)
      (C.restrictedChart D hD hC c).chart.openSet (C.restrictedChart D hD hC c).chart.equation
      (C.restrictedChart D hD hC c).chart.represents

/-- `[O_C(D|_C)]` is the Picard class of the cocycle extracted from the restricted atlas. -/
theorem restricted_toPic_eq_picardClass :
    (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC)).toPic =
      picardClass C.toScheme (fun c : C.GenericChart D => C.chartPreimage D c.1)
        (transitionUnits C.toScheme _ (C.restrictedLocalTrivializations D hD hC))
        (transitionUnits_isCocycle C.toScheme _ (C.restrictedLocalTrivializations D hD hC))
        (C.iSup_chartPreimage_eq_top D hD) :=
  InvertibleSheaf.toPic_eq_picardClass C.toScheme
    (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC))
    (C.restrictedLocalTrivializations D hD hC) (C.iSup_chartPreimage_eq_top D hD)

/-- The Picard-class bridge, reduced to a gauge equivalence of the two extracted cocycles
on the common cover `(i⁻¹U_c)_c`. -/
theorem toPic_eq_of_isGauge (b : ∀ c : C.GenericChart D, Γ(C.toScheme, C.chartPreimage D c.1)ˣ)
    (hb : IsGauge C.toScheme (fun c : C.GenericChart D => C.chartPreimage D c.1)
      (transitionUnits C.toScheme _ (C.pullbackLocalTrivializations D hD))
      (transitionUnits C.toScheme _ (C.restrictedLocalTrivializations D hD hC)) b) :
    (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D)).toPic =
      (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC)).toPic := by
  rw [C.pullback_toPic_eq_picardClass D hD, C.restricted_toPic_eq_picardClass D hD hC]
  exact picardClass_eq_of_gauge C.toScheme _ _ _ _ _ _ b hb

/-- The bridge from equality of the two extracted cocycles. -/
theorem toPic_eq_of_transitionUnits_eq
    (heq : transitionUnits C.toScheme _ (C.pullbackLocalTrivializations D hD) =
      transitionUnits C.toScheme _ (C.restrictedLocalTrivializations D hD hC)) :
    (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D)).toPic =
      (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC)).toPic := by
  refine C.toPic_eq_of_isGauge D hD hC (fun _ => 1) ?_
  intro c d
  simp only [Units.val_one, map_one, one_mul, mul_one, heq]

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
