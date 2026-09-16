import KltDP.Geometry.TransitionUnitLocalTriviality
import KltDP.Compatibility.InvertibleTensorUnit
import KltDP.Compatibility.ModuleTransitionUnit

/-!
# Section coordinates from an actual invertible-sheaf atlas

The chart coordinates are evaluations of the original module-sheaf
trivializations. They are linear over the original rings O(W), and both
directions commute with actual restrictions. These facts supply the
section-level input for extracting transition units.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitExtraction

open TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) (M : X.Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)

/-- Evaluating the original chart isomorphism gives coordinates over O(W). -/
def chartEquiv (i : t.I) {W : X.Opens} (hWi : W ≤ t.X i) :
    M.val.obj (op W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  ((_root_.PresheafOfModules.evaluation (X.ringCatSheaf.over (t.X i)).val
      (op (Over.mk (homOfLE hWi)))).mapIso
    ((_root_.SheafOfModules.forget (X.ringCatSheaf.over (t.X i))).mapIso
      (t.unitIso i))).toLinearEquiv

@[simp]
theorem chartEquiv_apply (i : t.I) {W : X.Opens} (hWi : W ≤ t.X i)
    (s : M.val.obj (op W)) :
    chartEquiv X M t i hWi s =
      (t.unitIso i).hom.val.app (op (Over.mk (homOfLE hWi))) s := rfl

@[simp]
theorem chartEquiv_symm_apply (i : t.I) {W : X.Opens} (hWi : W ≤ t.X i)
    (r : Γ(X, W)) :
    (chartEquiv X M t i hWi).symm r =
      (t.unitIso i).inv.val.app (op (Over.mk (homOfLE hWi))) r := rfl

/-- The chart coordinates commute with the original module-sheaf restrictions. -/
theorem chartEquiv_restrict (i : t.I) {V W : X.Opens}
    (hVW : V ≤ W) (hWi : W ≤ t.X i) (s : M.val.obj (op W)) :
    chartEquiv X M t i (hVW.trans hWi) (M.val.map (homOfLE hVW).op s) =
      res X hVW (chartEquiv X M t i hWi s) := by
  let f : Over.mk (homOfLE (hVW.trans hWi)) ⟶ Over.mk (homOfLE hWi) :=
    Over.homMk (homOfLE hVW)
  exact _root_.PresheafOfModules.naturality_apply (t.unitIso i).hom.val f.op s

/-- The inverse chart coordinates also commute with the original restrictions. -/
theorem chartEquiv_symm_restrict (i : t.I) {V W : X.Opens}
    (hVW : V ≤ W) (hWi : W ≤ t.X i) (r : Γ(X, W)) :
    (chartEquiv X M t i (hVW.trans hWi)).symm (res X hVW r) =
      M.val.map (homOfLE hVW).op ((chartEquiv X M t i hWi).symm r) := by
  let f : Over.mk (homOfLE (hVW.trans hWi)) ⟶ Over.mk (homOfLE hWi) :=
    Over.homMk (homOfLE hVW)
  exact _root_.PresheafOfModules.naturality_apply (t.unitIso i).inv.val f.op r

/-- The original local-trivialization covering sieve yields an actual open cover. -/
theorem chartOpens_cover : (⨆ i, t.X i) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨W, f, ⟨i, ⟨g⟩⟩, hxW⟩ := t.coversTop ⊤ x hx
  exact Opens.mem_iSup.mpr ⟨i, g.le hxW⟩

/-- The unit changing chart j to chart i on a common subopen. -/
def transitionUnitOn (i j : t.I) {W : X.Opens}
    (hWi : W ≤ t.X i) (hWj : W ≤ t.X j) : Γ(X, W)ˣ :=
  KltDP.Module.transitionUnit (chartEquiv X M t j hWj) (chartEquiv X M t i hWi)

/-- Transition units commute with the original section-ring restrictions. -/
theorem transitionUnitOn_restrict (i j : t.I) {V W : X.Opens}
    (hVW : V ≤ W) (hWi : W ≤ t.X i) (hWj : W ≤ t.X j) :
    res X hVW (transitionUnitOn X M t i j hWi hWj) =
      (transitionUnitOn X M t i j (hVW.trans hWi) (hVW.trans hWj) : Γ(X, V)) := by
  simp only [transitionUnitOn, KltDP.Module.transitionUnit_val]
  rw [← chartEquiv_restrict X M t i hVW hWi,
    ← chartEquiv_symm_restrict X M t j hVW hWj, map_one]

/-- The original atlas determines actual section-ring units on pairwise overlaps. -/
def transitionUnits (i j : t.I) : Γ(X, t.X i ⊓ t.X j)ˣ :=
  transitionUnitOn X M t i j inf_le_left inf_le_right

/-- The extracted unit gives the actual change of section coordinates on any subopen. -/
theorem transitionUnits_mul_chart (i j : t.I) {W : X.Opens}
    (hWi : W ≤ t.X i) (hWj : W ≤ t.X j) (s : M.val.obj (op W)) :
    res X (le_inf hWi hWj) (transitionUnits X M t i j) *
        chartEquiv X M t j hWj s = chartEquiv X M t i hWi s := by
  change res X (le_inf hWi hWj)
      (transitionUnitOn X M t i j inf_le_left inf_le_right) *
        chartEquiv X M t j hWj s = chartEquiv X M t i hWi s
  rw [transitionUnitOn_restrict X M t i j (le_inf hWi hWj) inf_le_left inf_le_right]
  exact KltDP.Module.transitionUnit_mul_apply
    (chartEquiv X M t j hWj) (chartEquiv X M t i hWi) s

/-- The actual transition units satisfy normalization and the triple-overlap equation. -/
theorem transitionUnits_isCocycle : IsCocycle X t.X (transitionUnits X M t) := by
  refine ⟨?_, ?_⟩
  · intro i
    change (KltDP.Module.transitionUnit
      (chartEquiv X M t i (inf_le_right : t.X i ⊓ t.X i ≤ t.X i))
      (chartEquiv X M t i (inf_le_left : t.X i ⊓ t.X i ≤ t.X i)) :
        Γ(X, t.X i ⊓ t.X i)) = 1
    simp only [KltDP.Module.transitionUnit_self, Units.val_one]
  · intro i j l
    let W : X.Opens := t.X i ⊓ t.X j ⊓ t.X l
    have hWi : W ≤ t.X i := inf_le_left.trans inf_le_left
    have hWj : W ≤ t.X j := inf_le_left.trans inf_le_right
    have hWl : W ≤ t.X l := inf_le_right
    let s : M.val.obj (op W) := (chartEquiv X M t l hWl).symm 1
    have hs : chartEquiv X M t l hWl s = 1 :=
      (chartEquiv X M t l hWl).apply_symm_apply 1
    have hj := transitionUnits_mul_chart X M t j l hWj hWl s
    have hi := transitionUnits_mul_chart X M t i j hWi hWj s
    have hil := transitionUnits_mul_chart X M t i l hWi hWl s
    rw [hs, mul_one] at hj hil
    change res X (le_inf hWi hWj) (transitionUnits X M t i j) *
      res X (le_inf hWj hWl) (transitionUnits X M t j l) =
        res X (le_inf hWi hWl) (transitionUnits X M t i l)
    calc
      _ = res X (le_inf hWi hWj) (transitionUnits X M t i j) *
          chartEquiv X M t j hWj s :=
        congrArg (fun a : Γ(X, W) =>
          res X (le_inf hWi hWj) (transitionUnits X M t i j) * a) hj
      _ = chartEquiv X M t i hWi s := hi
      _ = _ := hil.symm

/-- Extract the original overlap units from any actual invertible sheaf. -/
def invertibleSheafUnits (L : InvertibleSheaf X) :
    ∀ i j : L.localTrivializations.I,
      Γ(X, L.localTrivializations.X i ⊓ L.localTrivializations.X j)ˣ :=
  transitionUnits X L.obj L.localTrivializations

/-- The units extracted from an arbitrary invertible sheaf form a cocycle. -/
theorem invertibleSheafUnits_isCocycle (L : InvertibleSheaf X) :
    IsCocycle X L.localTrivializations.X (invertibleSheafUnits X L) :=
  transitionUnits_isCocycle X L.obj L.localTrivializations

/-- The extracted atlas covers the scheme by the original local-rank-one condition. -/
theorem invertibleSheafUnits_cover (L : InvertibleSheaf X) :
    (⨆ i, L.localTrivializations.X i) = ⊤ :=
  chartOpens_cover X L.obj L.localTrivializations

end KltDP.Geometry.TransitionUnitExtraction
