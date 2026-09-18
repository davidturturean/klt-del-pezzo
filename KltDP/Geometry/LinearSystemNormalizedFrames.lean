import KltDP.Geometry.LinearSystemAffineCharts
import KltDP.Geometry.TransitionUnitRecovery
import KltDP.Compatibility.SheafUnitAutomorphisms

/-!
# Original sheaf frames normalized by a finite linear system

On each original affine chart, divide the original frame by the unit
coefficient of the selected section. The resulting actual sheaf atlas
sends that section to one. Its extracted transition units are the original
normalized section coordinates, restricted to the actual overlaps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open TransitionUnitGluing TransitionUnitExtraction LinearSystemMorphism
  InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections)

local instance sectionCommRing (V : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj V) :=
  inferInstanceAs (CommRing (X.presheaf.obj V))

local instance : ∀ V, IsMulCommutative (X.ringCatSheaf.val.obj V) :=
  fun _ => ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The actual original frame scaled by the selected section's unit coefficient. -/
def normalizedFrame (c : Chart L s) :
    L.obj.over c.affineOpen.1 ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over c.affineOpen.1) :=
  L.localTrivializations.unitIsoOver c.frame (homOfLE c.inFrame) ≪≫
    KltDP.SheafOfModules.overUnitSectionUnitsEquivAut X.ringCatSheaf c.affineOpen.1
      (coefficient_isUnit L (s c.index) c.frame c.inFrame c.nonvanishing).unit⁻¹

/-- Every supplied original section has its original normalized coordinate in this frame. -/
theorem normalizedFrame_section (c : Chart L s) (j : Fin (n + 1)) :
    (normalizedFrame L s c).hom.val.app (op (Over.mk (𝟙 c.affineOpen.1)))
        ((s j).val (op c.affineOpen.1)) =
      coordinates L s c.frame c.inFrame c.index c.nonvanishing j := by
  change (KltDP.SheafOfModules.overUnitSectionUnitsEquivAut X.ringCatSheaf c.affineOpen.1
    (coefficient_isUnit L (s c.index) c.frame c.inFrame c.nonvanishing).unit⁻¹).hom.val.app
      (op (Over.mk (𝟙 c.affineOpen.1)))
      ((L.localTrivializations.unitIsoOver c.frame (homOfLE c.inFrame)).hom.val.app
        (op (Over.mk (𝟙 c.affineOpen.1))) ((s j).val (op c.affineOpen.1))) = _
  rw [KltDP.SheafOfModules.overUnitSectionUnitsEquivAut_hom_app_apply]
  change coefficient L (s j) c.frame c.inFrame *
    X.presheaf.map (𝟙 c.affineOpen.1).op
      (↑((coefficient_isUnit L (s c.index) c.frame c.inFrame c.nonvanishing).unit⁻¹)) = _
  rw [op_id, X.presheaf.map_id]
  change coefficient L (s j) c.frame c.inFrame *
    ↑((coefficient_isUnit L (s c.index) c.frame c.inFrame c.nonvanishing).unit⁻¹) = _
  exact mul_comm _ _

variable (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- The original chart cover equipped with the normalized actual unit frames. -/
def normalizedAtlas :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj where
  I := Chart L s
  X := fun c => c.affineOpen.1
  coversTop := opens_coversTop X _ (LinearSystemMorphism.chartOpens_cover L s hcover)
  iso c := _root_.SheafOfModules.freeUniqueIsoUnit
    (R := X.ringCatSheaf.over c.affineOpen.1) PUnit ≪≫ (normalizedFrame L s c).symm

theorem normalizedAtlas_unitIso (c : Chart L s) :
    (normalizedAtlas L s hcover).unitIso c = normalizedFrame L s c := by
  apply Iso.ext
  simp [KltDP.SheafOfModules.LocalTrivializations.unitIso, normalizedAtlas]

/-- At the chart itself the atlas coordinate is the normalized original coordinate. -/
theorem normalizedAtlas_chartEquiv_top (c : Chart L s) (j : Fin (n + 1)) :
    chartEquiv X L.obj (normalizedAtlas L s hcover) c le_rfl
        ((s j).val (op c.affineOpen.1)) =
      coordinates L s c.frame c.inFrame c.index c.nonvanishing j := by
  have h := congrArg
    (fun e : L.obj.over c.affineOpen.1 ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over c.affineOpen.1) =>
        e.hom.val.app (op (Over.mk (𝟙 c.affineOpen.1)))
          ((s j).val (op c.affineOpen.1)))
    (normalizedAtlas_unitIso L s hcover c)
  exact (chartEquiv_apply X L.obj (normalizedAtlas L s hcover) c le_rfl
    ((s j).val (op c.affineOpen.1))).trans (h.trans (normalizedFrame_section L s c j))

/-- The same formula holds after any original open restriction. -/
theorem normalizedAtlas_chartEquiv_section (c : Chart L s) {W : X.Opens}
    (hWc : W ≤ c.affineOpen.1) (j : Fin (n + 1)) :
    chartEquiv X L.obj (normalizedAtlas L s hcover) c hWc ((s j).val (op W)) =
      coordinates L s c.frame (hWc.trans c.inFrame) c.index
        (hWc.trans c.nonvanishing) j := by
  have hs : L.obj.val.map (homOfLE hWc).op ((s j).val (op c.affineOpen.1)) =
      (s j).val (op W) := (s j).property (homOfLE hWc).op
  exact (congrArg (chartEquiv X L.obj (normalizedAtlas L s hcover) c hWc) hs.symm).trans
    ((chartEquiv_restrict X L.obj (normalizedAtlas L s hcover) c hWc le_rfl
      ((s j).val (op c.affineOpen.1))).trans
        ((congrArg (res X hWc) (normalizedAtlas_chartEquiv_top L s hcover c j)).trans
          (coordinates_restrict L s c.frame hWc c.inFrame c.index c.nonvanishing j)))

/-- The actual extracted overlap unit is the ratio of the two selected sections. -/
theorem normalizedAtlas_transitionUnits_val (c d : Chart L s) :
    ((transitionUnits X L.obj (normalizedAtlas L s hcover) c d).val :
        Γ(X, c.affineOpen.1 ⊓ d.affineOpen.1)) =
      res X inf_le_left
        (coordinates L s c.frame c.inFrame c.index c.nonvanishing d.index) := by
  let W : X.Opens := c.affineOpen.1 ⊓ d.affineOpen.1
  let v : Γ(X, W) := (transitionUnits X L.obj (normalizedAtlas L s hcover) c d).val
  have hc : W ≤ c.affineOpen.1 := inf_le_left
  have hd : W ≤ d.affineOpen.1 := inf_le_right
  have hres : res X (le_inf hc hd) v = v := res_self X W v
  have hd1 : chartEquiv X L.obj (normalizedAtlas L s hcover) d hd
      ((s d.index).val (op W)) = 1 :=
    (normalizedAtlas_chartEquiv_section L s hcover d hd d.index).trans
      (coordinates_self L s d.frame (hd.trans d.inFrame) d.index (hd.trans d.nonvanishing))
  have hcoord : v = coordinates L s c.frame (hc.trans c.inFrame) c.index
      (hc.trans c.nonvanishing) d.index := by
    calc
      v = v * 1 := (mul_one v).symm
      _ = res X (le_inf hc hd) v *
          chartEquiv X L.obj (normalizedAtlas L s hcover) d hd
            ((s d.index).val (op W)) :=
        congrArg₂ (fun a b : Γ(X, W) => a * b) hres.symm hd1.symm
      _ = chartEquiv X L.obj (normalizedAtlas L s hcover) c hc
          ((s d.index).val (op W)) :=
        transitionUnits_mul_chart X L.obj (normalizedAtlas L s hcover) c d hc hd _
      _ = _ := normalizedAtlas_chartEquiv_section L s hcover c hc d.index
  exact hcoord.trans (coordinates_restrict L s c.frame hc c.inFrame c.index
    c.nonvanishing d.index).symm

/-- The original sheaf is the matching-coordinate sheaf of this normalized atlas. -/
def normalizedRecoveryIso : L.obj ≅
    moduleSheaf X (fun c : Chart L s => c.affineOpen.1)
      (transitionUnits X L.obj (normalizedAtlas L s hcover)) :=
  recoveryIso X L.obj (normalizedAtlas L s hcover)

end KltDP.Geometry.LinearSystemPullback
