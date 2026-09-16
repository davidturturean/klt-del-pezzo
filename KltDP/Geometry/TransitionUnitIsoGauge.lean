import KltDP.Geometry.TransitionUnitGauge

/-!
# Extracting actual gauge units from an actual sheaf isomorphism

An isomorphism between two sheaves glued on the same actual chart family
induces an automorphism of the unit sheaf on each chart. The proved
section-unit/automorphism equivalence extracts an original chart unit.
Evaluating the original morphism shows that these units satisfy the
gauge equation. No gauge or chart-unit existence is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g h : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)
  (hg : IsCocycle X U g) (hh : IsCocycle X U h)
  (e : moduleSheaf X U g ≅ moduleSheaf X U h)

local instance isoGaugeSectionCommRing (V : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj V) :=
  inferInstanceAs (CommRing (X.presheaf.obj V))

local instance : ∀ V, IsMulCommutative (X.ringCatSheaf.val.obj V) :=
  fun _ => ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The original sheaf isomorphism expressed in the two actual chart frames. -/
def isoChartAutomorphism (i : ι) :
    Aut (_root_.SheafOfModules.unit (X.ringCatSheaf.over (U i))) :=
  (chartIsoOn X U g hg i le_rfl).symm ≪≫
    (_root_.SheafOfModules.overFunctor X.ringCatSheaf (U i)).mapIso e ≪≫
      chartIsoOn X U h hh i le_rfl

/-- The actual section unit underlying the chart automorphism. -/
def isoChartUnit (i : ι) : Γ(X, U i)ˣ :=
  (KltDP.SheafOfModules.overUnitSectionUnitsEquivAut X.ringCatSheaf (U i)).symm
    (isoChartAutomorphism X U g h hg hh e i)

/-- Multiplying coordinates by the extracted unit is the original morphism on every subopen. -/
theorem isoChartUnit_mul (i : ι) {W : X.Opens} (hWi : W ≤ U i)
    (s : sections X U g W) :
    res X hWi (isoChartUnit X U g h hg hh e i) * trivialization X U g hg i hWi s =
      trivialization X U h hh i hWi (e.hom.val.app (op W) s) := by
  have he := (KltDP.SheafOfModules.overUnitSectionUnitsEquivAut
    X.ringCatSheaf (U i)).apply_symm_apply (isoChartAutomorphism X U g h hg hh e i)
  have ht := congrArg (fun a : Aut (_root_.SheafOfModules.unit (X.ringCatSheaf.over (U i))) =>
    a.hom.val.app (op (Over.mk (homOfLE hWi))) (trivialization X U g hg i hWi s)) he
  dsimp only at ht
  rw [KltDP.SheafOfModules.overUnitSectionUnitsEquivAut_hom_app_apply] at ht
  change trivialization X U g hg i hWi s * res X hWi (isoChartUnit X U g h hg hh e i) =
    trivialization X U h hh i hWi
      (e.hom.val.app (op W) ((trivialization X U g hg i hWi).symm
        (trivialization X U g hg i hWi s))) at ht
  rw [LinearEquiv.symm_apply_apply, mul_comm] at ht
  exact ht

/-- The chart units extracted from an actual isomorphism satisfy the original gauge equations. -/
theorem isoChartUnit_isGauge :
    IsGauge X U g h (isoChartUnit X U g h hg hh e) := by
  intro i j
  let W := U i ⊓ U j
  let s : sections X U g W := (trivialization X U g hg j inf_le_right).symm 1
  have hs : trivialization X U g hg j inf_le_right s = 1 :=
    (trivialization X U g hg j inf_le_right).apply_symm_apply 1
  have hsi : trivialization X U g hg i inf_le_left s = (g i j : Γ(X, W)) := by
    rw [trivialization_transition X U g hg i j inf_le_left inf_le_right, hs,
      mul_one, res_self]
  calc
    res X inf_le_left (isoChartUnit X U g h hg hh e i) * (g i j : Γ(X, W)) =
        res X inf_le_left (isoChartUnit X U g h hg hh e i) *
          trivialization X U g hg i inf_le_left s := by rw [hsi]
    _ = trivialization X U h hh i inf_le_left (e.hom.val.app (op W) s) :=
      isoChartUnit_mul X U g h hg hh e i inf_le_left s
    _ = (h i j : Γ(X, W)) *
        trivialization X U h hh j inf_le_right (e.hom.val.app (op W) s) := by
      rw [trivialization_transition X U h hh i j inf_le_left inf_le_right, res_self]
    _ = (h i j : Γ(X, W)) * res X inf_le_right (isoChartUnit X U g h hg hh e j) := by
      rw [← isoChartUnit_mul X U g h hg hh e j inf_le_right s, hs, mul_one]

include hg hh e in
/-- The actual sheaf isomorphism produces a gauge witness on the original cover. -/
theorem exists_gauge_of_iso : ∃ b : ∀ i : ι, Γ(X, U i)ˣ, IsGauge X U g h b :=
  ⟨isoChartUnit X U g h hg hh e, isoChartUnit_isGauge X U g h hg hh e⟩

end KltDP.Geometry.TransitionUnitGluing
