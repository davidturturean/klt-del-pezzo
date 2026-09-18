import KltDP.Geometry.EffectiveCartierSectionSupport
import KltDP.Geometry.InvertibleSectionNonvanishingOpen
import KltDP.Geometry.SchemeModulePullbackUnit

/-! The original canonical section is nonvanishing exactly off the
actual Cartier ideal support. The comparison uses the same regular
equation, original frame, and compatible family of section restrictions. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open InvertibleSectionNonvanishingOpen TransitionUnitExtraction

variable (X : Scheme.{u}) [IsIntegral X]

/-- The original Cartier atlas has exactly the original equation frame. -/
theorem cartierLocalTrivializations_unitIso_hom (D : CartierDivisor X)
    (c : CartierEquationChart X D) :
    ((cartierDivisorLocalTrivializations X D).unitIso c).hom =
      (cartierEquationOverIso X D c.openSet c.equation c.represents).inv := by
  let a := _root_.SheafOfModules.freeUniqueIsoUnit
    (R := X.ringCatSheaf.over c.openSet) PUnit
  let τ := cartierEquationOverIso X D c.openSet c.equation c.represents
  change (τ.inv ≫ a.inv) ≫ a.hom = τ.inv
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- For any original module and atlas, the coefficient of a compatible
family from a top section is the actual frame evaluation of its restriction. -/
theorem chartCoefficient_top_eq_evalSection (M : X.Modules)
    (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)
    (s : M.val.obj (op (⊤ : X.Opens))) (i : t.I) :
    chartCoefficient X M t (schemeModuleSectionOfTop M s) i =
      KltDP.SheafOfModules.evalSection X.ringCatSheaf M (t.X i) (t.unitIso i).hom
        (M.val.map (homOfLE (le_top : t.X i ≤ ⊤)).op s) := by
  let U : X.Opens := t.X i
  let r : M.val.obj (op U) := M.val.map (homOfLE (le_top : U ≤ ⊤)).op s
  have hid : M.val.map (𝟙 U).op r = r :=
    CategoryTheory.congr_fun (M.val.presheaf.map_id (op U)) r
  change (t.unitIso i).hom.val.app (op (Over.mk (𝟙 U))) r =
    (t.unitIso i).hom.val.app (op (Over.mk (𝟙 U))) (M.val.map (𝟙 U).op r)
  exact congrArg ((t.unitIso i).hom.val.app (op (Over.mk (𝟙 U)))) hid.symm

/-- The original Cartier atlas evaluation is the original equation-frame
evaluation, for every top section of the same original divisor module. -/
theorem cartierChartCoefficient_top_eq_frameEvaluation (D : CartierDivisor X)
    (s : (cartierDivisorModule X D).val.obj (op (⊤ : X.Opens)))
    (c : CartierEquationChart X D) :
    chartCoefficient X (cartierDivisorModule X D) (cartierDivisorLocalTrivializations X D)
      (schemeModuleSectionOfTop (cartierDivisorModule X D) s) c =
      KltDP.SheafOfModules.evalSection X.ringCatSheaf (cartierDivisorModule X D) c.openSet
        (cartierEquationOverIso X D c.openSet c.equation c.represents).inv
        ((cartierDivisorModule X D).val.map (homOfLE (le_top : c.openSet ≤ ⊤)).op s) := by
  refine (chartCoefficient_top_eq_evalSection X (cartierDivisorModule X D)
    (cartierDivisorLocalTrivializations X D) s c).trans ?_
  exact congrArg (fun f : (cartierDivisorModule X D).over c.openSet ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over c.openSet) =>
    KltDP.SheafOfModules.evalSection X.ringCatSheaf (cartierDivisorModule X D) c.openSet f
      ((cartierDivisorModule X D).val.map (homOfLE (le_top : c.openSet ≤ ⊤)).op s))
    (cartierLocalTrivializations_unitIso_hom X D c)

/-- The intrinsic nonvanishing coefficient is the same regular
equation used to construct the actual divisor ideal. -/
theorem effectiveCartierSection_chartCoefficient (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (c : RegularCartierEquationChart X D) :
    chartCoefficient X (cartierDivisorModule X D) (cartierDivisorLocalTrivializations X D)
      (schemeModuleSectionOfTop (cartierDivisorModule X D) (effectiveCartierSection X D hD))
      c.chart = c.coefficient :=
  (cartierChartCoefficient_top_eq_frameEvaluation X D (effectiveCartierSection X D hD) c.chart).trans
    (effectiveCartierSection_frame_eval X D hD c)

/-- The actual canonical section vanishes precisely on the original
Cartier ideal support, with no support comparison supplied. -/
theorem effectiveCartierSection_mem_nonvanishing_iff (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D) (x : X) :
    x ∈ nonvanishingOpen X (cartierDivisorInvertibleSheaf X D)
      (schemeModuleSectionOfTop (cartierDivisorModule X D) (effectiveCartierSection X D hD)) ↔
      x ∉ (effectiveCartierIdealDataOfRegularEquations X D hD).support := by
  obtain ⟨c, hxc⟩ := hD x
  have hnonvan := mem_nonvanishingOpen_iff_isUnit_germ X (cartierDivisorInvertibleSheaf X D)
    (schemeModuleSectionOfTop (cartierDivisorModule X D) (effectiveCartierSection X D hD))
    (cartierDivisorLocalTrivializations X D) c.chart x hxc
  change _ ↔ IsUnit (X.presheaf.germ c.chart.openSet x hxc
    (chartCoefficient X (cartierDivisorModule X D)
      (cartierDivisorLocalTrivializations X D)
      (schemeModuleSectionOfTop (cartierDivisorModule X D)
        (effectiveCartierSection X D hD)) c.chart)) at hnonvan
  rw [effectiveCartierSection_chartCoefficient X D hD c] at hnonvan
  have hsupp := NormalProjectiveSurface.PrimeCurve.mem_support_iff_not_isUnit_germ D hD c x hxc
  constructor
  · intro hx hx'
    exact hsupp.mp hx' (hnonvan.mp hx)
  · intro hx
    apply hnonvan.mpr
    by_contra hn
    exact hx (hsupp.mpr hn)

end KltDP.Geometry

#check @KltDP.Geometry.effectiveCartierSection_mem_nonvanishing_iff
#print axioms KltDP.Geometry.effectiveCartierSection_mem_nonvanishing_iff
