import KltDP.Examples.FrobeniusExceptionalAdjacentTransport
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The original exceptional curves in one final blowup scheme

The actual one-step projections form the pinned inverse-sequence functor.
Its maps identify each original later-curve lift with a closed curve in the
same final scheme. The original adjacent point remains on the next actual
strict transform. Nonadjacent curves are disjoint by projecting to the
creation stage of the newer fiber. No intersection pairing is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusExceptionalFinalConfiguration

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalSuccessor
open FrobeniusExceptionalLaterStages FrobeniusExceptionalAdjacentTransport

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The inverse sequence consists of the original whole blowup projections. -/
def stageDiagram : ℕᵒᵖ ⥤ Scheme.{u} :=
  Functor.ofOpSequence (X := fun n => (A.stage n).carrier) A.stepProjection

/-- The original composite projection between two specified whole stages. -/
def between {i j : ℕ} (h : i ≤ j) :
    (A.stage j).carrier ⟶ (A.stage i).carrier :=
  (stageDiagram A).map (homOfLE h).op

@[simp] theorem between_refl (i : ℕ) : between A (le_refl i) = 𝟙 _ := by
  change (stageDiagram A).map (𝟙 _) = _
  exact (stageDiagram A).map_id _

@[simp] theorem between_step (i : ℕ) :
    between A (show i ≤ i + 1 by omega) = A.stepProjection i :=
  Functor.ofOpSequence_map_homOfLE_succ (X := fun n => (A.stage n).carrier)
    A.stepProjection i

@[reassoc] theorem between_comp {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) :
    between A hjl ≫ between A hij = between A (hij.trans hjl) := by
  unfold between
  rw [← Functor.map_comp]
  rfl

theorem between_succ {i j : ℕ} (h : i ≤ j) :
    between A (show i ≤ j + 1 by omega) =
      A.stepProjection j ≫ between A h := by
  rw [← between_step]
  exact (between_comp A h (show j ≤ j + 1 by omega)).symm

@[simp] theorem between_zero (n : ℕ) :
    between A (Nat.zero_le n) = A.toInitial n := by
  induction n with
  | zero => rw [between_refl, PlaneChartedScheme.toInitial_zero]; rfl
  | succ n ih =>
      rw [between_succ A (Nat.zero_le n), ih, PlaneChartedScheme.toInitial_succ]

/-- Restarting the original recursion at stage `b` gives its actual later stages. -/
theorem stage_add (b m : ℕ) : (A.stage b).stage m = A.stage (b + m) := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg PlaneChartedScheme.next ih

private theorem nextProjection_congr {B C : PlaneChartedScheme k} (h : B = C) :
    eqToHom (congrArg (fun T : PlaneChartedScheme k => T.next.carrier) h) ≫
        C.nextProjection =
      B.nextProjection ≫ eqToHom (congrArg PlaneChartedScheme.carrier h) := by
  subst C
  simp

/-- Equality transport only reindexes the original carrier. -/
def stageAddIso (b m : ℕ) :
    ((A.stage b).stage m).carrier ≅ (A.stage (b + m)).carrier :=
  eqToIso (congrArg PlaneChartedScheme.carrier (stage_add A b m))

@[reassoc] theorem stageAddIso_step (b m : ℕ) :
    (stageAddIso A b (m + 1)).hom ≫ A.stepProjection (b + m) =
      (A.stage b).stepProjection m ≫ (stageAddIso A b m).hom :=
  nextProjection_congr (stage_add A b m)

@[reassoc] theorem stageAddIso_hom_between (b m : ℕ) :
    (stageAddIso A b m).hom ≫ between A (show b ≤ b + m by omega) =
      (A.stage b).toInitial m := by
  induction m with
  | zero => simp [stageAddIso, PlaneChartedScheme.toInitial_zero, PlaneChartedScheme.stage]
  | succ m ih =>
      rw [between_succ A (show b ≤ b + m by omega), ← Category.assoc,
        stageAddIso_step, Category.assoc, ih, PlaneChartedScheme.toInitial_succ]

/-- The same reindexing when the final stage is specified by an inequality. -/
def stageFinishIso (b N : ℕ) (h : b ≤ N) :
    ((A.stage b).stage (N - b)).carrier ≅ (A.stage N).carrier :=
  eqToIso (congrArg PlaneChartedScheme.carrier
    ((stage_add A b (N - b)).trans (congrArg A.stage (by omega))))

@[reassoc] theorem stageFinishIso_hom_between (b N : ℕ) (h : b ≤ N) :
    (stageFinishIso A b N h).hom ≫ between A h =
      (A.stage b).toInitial (N - b) := by
  let m := N - b
  have H : ∀ (q : ℕ) (he : b + m = q),
      (eqToIso (congrArg PlaneChartedScheme.carrier
        ((stage_add A b m).trans (congrArg A.stage he)))).hom ≫
          between A (show b ≤ q by omega) = (A.stage b).toInitial m := by
    intro q he
    subst q
    exact stageAddIso_hom_between A b m
  exact H N (by dsimp [m]; omega)

/-- An earlier original strict curve, embedded into the specified final scheme. -/
def finalOldMap (N j : ℕ) (h : j + 2 ≤ N) :
    previousStrictTransform (A.stage j) ⟶ (A.stage N).carrier :=
  laterCurveMap (A.stage j) (N - (j + 2)) ≫
    (stageFinishIso A (j + 2) N h).hom

instance finalOldMap_isClosedImmersion (N j : ℕ) (h : j + 2 ≤ N) :
    IsClosedImmersion (finalOldMap A N j h) := by
  unfold finalOldMap
  infer_instance

@[reassoc] theorem finalOldMap_projection (N j : ℕ) (h : j + 2 ≤ N) :
    finalOldMap A N j h ≫ between A h = previousStrictι (A.stage j) := by
  rw [finalOldMap, Category.assoc, stageFinishIso_hom_between]
  exact laterCurveMap_projection (A.stage j) _

/-- The final embedding is the literal pullback of the original strict curve.
All later centers are off that curve; the source is unchanged. -/
theorem finalOldMap_isPullback (N j : ℕ) (h : j + 2 ≤ N) :
    IsPullback (finalOldMap A N j h) (𝟙 (previousStrictTransform (A.stage j)))
      (between A h) (previousStrictι (A.stage j)) := by
  refine (laterCurveMap_isPullback (A.stage j) (N - (j + 2))).of_iso
    (Iso.refl _) (stageFinishIso A (j + 2) N h) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, finalOldMap]
  · simp only [Iso.refl_hom]
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (stageFinishIso_hom_between A (j + 2) N h).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem finalOldMap_eq_of_projection (N j : ℕ) (hj : j + 2 ≤ N)
    {Z : Scheme.{u}} (f : Z ⟶ (A.stage N).carrier)
    (q : Z ⟶ previousStrictTransform (A.stage j))
    (w : f ≫ between A hj = q ≫ previousStrictι (A.stage j)) :
    f = q ≫ finalOldMap A N j hj := by
  let H := finalOldMap_isPullback A N j hj
  have hs : H.lift f q w = q := by
    simpa only [Category.comp_id] using H.lift_snd f q w
  calc
    f = H.lift f q w ≫ finalOldMap A N j hj := (H.lift_fst f q w).symm
    _ = q ≫ finalOldMap A N j hj := by rw [hs]

/-- Projection to any intermediate stage preserves the same original embedding. -/
@[reassoc] theorem finalOldMap_between {N M j : ℕ}
    (hj : j + 2 ≤ M) (hMN : M ≤ N) :
    finalOldMap A N j (hj.trans hMN) ≫ between A hMN = finalOldMap A M j hj := by
  have h := finalOldMap_eq_of_projection A M j hj
    (finalOldMap A N j (hj.trans hMN) ≫ between A hMN) (𝟙 _) (by
      rw [Category.assoc, between_comp, finalOldMap_projection, Category.id_comp])
  simpa only [Category.id_comp] using h

@[simp] theorem finalOldMap_birth (j : ℕ) :
    finalOldMap A (j + 2) j (le_refl _) = previousStrictι (A.stage j) := by
  simpa only [between_refl, Category.comp_id] using
    finalOldMap_projection A (j + 2) j (le_refl _)

@[simp] theorem finalOldMap_one (j : ℕ) :
    finalOldMap A (j + 3) j (by omega) = laterCurveMap (A.stage j) 1 := by
  have h := finalOldMap_eq_of_projection A (j + 3) j (by omega)
    (laterCurveMap (A.stage j) 1) (𝟙 _) (by
      rw [between_step A (j + 2), Category.id_comp]
      simpa only [laterCurveMap_zero] using laterCurveMap_step (A.stage j) 0)
  simpa only [Category.id_comp] using h.symm

/-- The actual pullback determines the full closed image, not only a chosen point. -/
theorem range_finalOldMap (N j : ℕ) (h : j + 2 ≤ N) :
    Set.range (finalOldMap A N j h).base =
      (between A h).base ⁻¹' Set.range (previousStrictι (A.stage j)).base := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    exact (congrArg (fun f => f.base z) (finalOldMap_projection A N j h)).symm
  · rintro ⟨z, hz⟩
    let H := finalOldMap_isPullback A N j h
    obtain ⟨p, hp, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := between A h) (g := previousStrictι (A.stage j)) x z hz.symm
    refine ⟨H.isoPullback.inv.base p, ?_⟩
    change (H.isoPullback.inv ≫ finalOldMap A N j h).base p = x
    rw [H.isoPullback_inv_fst]
    exact hp

/-- Membership in the same original strict curve can be checked at any
intermediate stage after its strict transform was constructed. -/
theorem mem_finalOldMap_iff {N M j : ℕ} (hj : j + 2 ≤ M) (hMN : M ≤ N)
    (x : (A.stage N).carrier) :
    x ∈ Set.range (finalOldMap A N j (hj.trans hMN)).base ↔
      (between A hMN).base x ∈ Set.range (finalOldMap A M j hj).base := by
  rw [range_finalOldMap, range_finalOldMap]
  change (between A (hj.trans hMN)).base x ∈
      Set.range (previousStrictι (A.stage j)).base ↔
    (between A hMN ≫ between A hj).base x ∈
      Set.range (previousStrictι (A.stage j)).base
  rw [between_comp]

private theorem avoids_chart_transport {B C : PlaneChartedScheme k} (h : B = C)
    {Z : Scheme.{u}} (f : Z ⟶ B.carrier)
    (hf : ∀ z, f.base z ∉ Set.range B.chart.base) :
    ∀ z, (f ≫ eqToHom (congrArg PlaneChartedScheme.carrier h)).base z ∉
      Set.range C.chart.base := by
  subst C
  simpa only [eqToHom_refl, Category.comp_id] using hf

/-- The entire final old component avoids the final selected plane chart. -/
theorem finalOldMap_avoids_chart (N j : ℕ) (h : j + 2 ≤ N)
    (z : previousStrictTransform (A.stage j)) :
    (finalOldMap A N j h).base z ∉ Set.range (A.stage N).chart.base := by
  exact avoids_chart_transport
    ((stage_add A (j + 2) (N - (j + 2))).trans (congrArg A.stage (by omega)))
    (laterCurveMap (A.stage j) (N - (j + 2)))
    (laterCurveMap_avoids_chart (A.stage j) (N - (j + 2))) z

/-- A component already strict before a blowup is disjoint from its newly
created actual center fiber. -/
theorem finalOld_disjoint_newest (n j : ℕ) (h : j + 2 ≤ n) :
    Disjoint (Set.range (finalOldMap A (n + 1) j (by omega)).base)
      (Set.range (previousFiberι (A.stage n)).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ hz
  change (finalOldMap A (n + 1) j (by omega)).base z ∈
    Set.range (PointBlowupGluing.globalCenterFiberι (A.stage n).chart
      (originPoint (k := k)) (A.stage n).center_closed).base at hz
  rw [PointBlowupGluing.range_globalCenterFiberι] at hz
  have hz' : (A.stepProjection n).base
      ((finalOldMap A (n + 1) j (by omega)).base z) =
        (A.stage n).chart.base (originPoint (k := k)) := hz
  have he := congrArg (fun f => f.base z)
    (finalOldMap_between A h (show n ≤ n + 1 by omega))
  rw [between_step] at he
  exact finalOldMap_avoids_chart A n j h z
    ⟨originPoint (k := k), hz'.symm.trans he⟩

/-- The final newer strict component still projects into its actual original
creation fiber. This uses the whole-curve closure theorem. -/
theorem finalOldMap_projection_mem_fiber (N j : ℕ) (h : j + 2 ≤ N)
    (z : previousStrictTransform (A.stage j)) :
    (between A (show j + 1 ≤ N by omega)).base ((finalOldMap A N j h).base z) ∈
      Set.range (previousFiberι (A.stage j)).base := by
  rw [← between_comp A (show j + 1 ≤ j + 2 by omega) h, between_step]
  change ((finalOldMap A N j h ≫ between A h) ≫ A.stepProjection (j + 1)).base z ∈ _
  rw [finalOldMap_projection]
  exact previousStrict_projection_mem_previousFiber (A.stage j) z

/-- Nonadjacent original strict components have disjoint whole closed images
in the same final scheme. -/
theorem finalOld_disjoint_finalOld (N i j : ℕ) (hij : i + 1 < j)
    (hj : j + 2 ≤ N) :
    Disjoint (Set.range (finalOldMap A N i (by omega)).base)
      (Set.range (finalOldMap A N j hj).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hxy⟩
  have hy := finalOldMap_projection_mem_fiber A N j hj y
  rw [hxy] at hy
  have hi : i + 2 ≤ j + 1 := by omega
  have hN : j + 1 ≤ N := by omega
  have he := congrArg (fun f => f.base x) (finalOldMap_between A hi hN)
  change (between A hN).base ((finalOldMap A N i (by omega)).base x) =
    (finalOldMap A (j + 1) i hi).base x at he
  rw [he] at hy
  exact (Set.disjoint_left.mp (finalOld_disjoint_newest A j i (by omega)))
    ⟨x, rfl⟩ hy

/-- The original adjacent point lies on both actual strict components in
every common final stage. -/
theorem finalOld_adjacent (N j : ℕ) (h : j + 3 ≤ N) :
    (finalOldMap A N j (by omega)).base (adjacentPoint (A.stage j)) ∈
      Set.range (finalOldMap A N (j + 1) h).base := by
  apply (mem_finalOldMap_iff A (j := j + 1) (le_refl (j + 3)) h _).mpr
  have he := congrArg (fun f => f.base (adjacentPoint (A.stage j)))
    (finalOldMap_between A (show j + 2 ≤ j + 3 by omega) h)
  change (between A h).base
      ((finalOldMap A N j (by omega)).base (adjacentPoint (A.stage j))) =
    (finalOldMap A (j + 3) j (by omega)).base (adjacentPoint (A.stage j)) at he
  rw [he, finalOldMap_one, finalOldMap_birth]
  exact laterAdjacentPoint_mem_nextStrict (A.stage j)

/-- The last old strict component and the newest original fiber meet at
their actual original parameter-zero point. -/
theorem finalOld_adjacent_newest (j : ℕ) :
    (finalOldMap A (j + 2) j (le_refl _)).base (adjacentPoint (A.stage j)) ∈
      Set.range (previousFiberι (A.stage (j + 1))).base := by
  rw [finalOldMap_birth]
  exact adjacentPoint_mem_newFiber (A.stage j)

/-- Indices for the `n` earlier original strict curves and the newest fiber
after `n+1` blowups. No curve family is an input. -/
abbrev FinalIndex (n : ℕ) := Fin n ⊕ PUnit

/-- Each component is an existing original scheme, with no replacement model. -/
def finalComponent (n : ℕ) : FinalIndex n → Scheme.{u}
  | .inl j => previousStrictTransform (A.stage j.val)
  | .inr _ => previousFiber (A.stage n)

/-- Every indexed original component has its actual closed embedding into
the same final whole scheme. -/
def finalComponentι (n : ℕ) : (a : FinalIndex n) →
    finalComponent A n a ⟶ (A.stage (n + 1)).carrier
  | .inl j => finalOldMap A (n + 1) j.val (by omega)
  | .inr _ => previousFiberι (A.stage n)

instance finalComponentι_isClosedImmersion (n : ℕ) (a : FinalIndex n) :
    IsClosedImmersion (finalComponentι A n a) := by
  cases a with
  | inl j => change IsClosedImmersion (finalOldMap A (n + 1) j.val _); infer_instance
  | inr t => change IsClosedImmersion (previousFiberι (A.stage n)); infer_instance

/-- The actual closed support of each indexed original embedding. -/
def finalSupport (n : ℕ) (a : FinalIndex n) : Set (A.stage (n + 1)).carrier :=
  Set.range (finalComponentι A n a).base

theorem finalSupport_isClosed (n : ℕ) (a : FinalIndex n) :
    IsClosed (finalSupport A n a) :=
  (finalComponentι A n a).isClosedEmbedding.isClosed_range

/-- Adjacent earlier indexed components meet in the common final scheme. -/
theorem finalSupport_adjacent (n j : ℕ) (hj : j + 1 < n) :
    (finalSupport A n (.inl ⟨j, by omega⟩) ∩
      finalSupport A n (.inl ⟨j + 1, hj⟩)).Nonempty := by
  refine ⟨(finalOldMap A (n + 1) j (by omega)).base (adjacentPoint (A.stage j)),
    ⟨adjacentPoint (A.stage j), rfl⟩, ?_⟩
  exact finalOld_adjacent A (n + 1) j (by omega)

/-- The last indexed earlier component meets the newest actual fiber. -/
theorem finalSupport_last_adjacent (n : ℕ) :
    (finalSupport A (n + 1) (.inl ⟨n, by omega⟩) ∩
      finalSupport A (n + 1) (.inr PUnit.unit)).Nonempty := by
  refine ⟨(finalOldMap A (n + 2) n (le_refl _)).base (adjacentPoint (A.stage n)),
    ⟨adjacentPoint (A.stage n), rfl⟩, ?_⟩
  exact finalOld_adjacent_newest A n

/-- Nonadjacent earlier indexed components are disjoint. -/
theorem finalSupport_nonadjacent (n : ℕ) (i j : Fin n) (hij : i.val + 1 < j.val) :
    Disjoint (finalSupport A n (.inl i)) (finalSupport A n (.inl j)) :=
  finalOld_disjoint_finalOld A (n + 1) i.val j.val hij (by omega)

/-- An earlier component separated from the newest one is disjoint from it. -/
theorem finalSupport_nonadjacent_newest (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    Disjoint (finalSupport A n (.inl i)) (finalSupport A n (.inr PUnit.unit)) :=
  finalOld_disjoint_newest A n i.val (by omega)

end KltDP.Examples.FrobeniusExceptionalFinalConfiguration
