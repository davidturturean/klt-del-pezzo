import KltDP.Geometry.SchemePullbackOverOpenIso
import KltDP.Examples.FrobeniusMultiCentreSurface

/-!
# The exceptional curves of `S_{p,n}` as actual closed subschemes

Write `p = q + 1`. On the multi-centre surface `S_{p,n} = multiSurface (q+1) n a` (lane F), the
`i`-th tower `T_i` carries the accepted final exceptional configuration
`FrobeniusExceptionalFinalConfiguration.finalComponentι A q idx` (`A := translatedInitial (q+1) (a i)`):
for `idx = Sum.inl j` (`j : Fin q`) the whole strict transform `C_{i,j+1}` of the exceptional curve
created at blowup `j+1`, for `idx = Sum.inr _` the newest fibre `P_i = E_{ip}`. This module defines

`exceptionalCurve q n a i idx := pullback (towerProjection (q+1) n a i) (finalComponentι A q idx)`

with its closed immersion `exceptionalCurveι` into `S_{p,n}` (base change of the accepted closed
immersion), and proves, for an injective selection `a` over an algebraically closed field:

* the second projection `exceptionalCurve ⟶ finalComponent A q idx` is an isomorphism, because the
  tower projection `S_{p,n} ⟶ T_i` is an isomorphism over the complement of the other centres
  (`towerProjection_restrict_isIso`), where every exceptional curve of `T_i` lives (it lies over the
  centre `(a i, (a i)^p)`); hence `P_i ≅ P¹` and `P_i` is integral (accepted `previousFiberIso`,
  `previousFiber_isIntegral`), and `C_{ij}` is isomorphic to the accepted reduced strict transform;
* every point of an exceptional curve projects to its centre in `P¹ ×_k P¹`, so curves from
  different towers are disjoint;
* inside one tower the accepted incidences transport: adjacent `C_{ij}`, `C_{i,j+1}` meet,
  `C_{i,q}` meets `P_i`, non-adjacent components are disjoint, and `P_i` is disjoint from every
  `C_{ij}` with `j + 1 < q`.

Not proved here: that `C_{ij}` is isomorphic to `P¹` (the accepted library only gives reducedness
of the older exceptional strict transforms), that the adjacent intersections are single points, and
any intersection number. Nothing about the curves is assumed; every incidence is transported from an
accepted statement through the actual base-change isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptional

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusContactTowerSelectedPoint
  FrobeniusGlobalExceptionalSuccessor FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreSurface

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

section Tower

variable (A : PlaneChartedScheme k)

/-- Every point of an earlier exceptional component projects to the original centre. -/
theorem finalOldMap_projection_center (N j : ℕ) (h : j + 2 ≤ N)
    (z : previousStrictTransform (A.stage j)) :
    (A.toInitial N).base ((finalOldMap A N j h).base z) = A.chart.base (originPoint (k := k)) := by
  have hfib := finalOldMap_projection_mem_fiber A N j h z
  change _ ∈ Set.range (PointBlowupGluing.globalCenterFiberι
    (A.stage j).chart (originPoint (k := k)) (A.stage j).center_closed).base at hfib
  rw [PointBlowupGluing.range_globalCenterFiberι] at hfib
  have hstep : (A.stepProjection j).base
      ((between A (show j + 1 ≤ N by omega)).base ((finalOldMap A N j h).base z)) =
      (A.stage j).chart.base (originPoint (k := k)) := hfib
  have hb : A.toInitial N =
      between A (show j + 1 ≤ N by omega) ≫ A.stepProjection j ≫ A.toInitial j := by
    rw [← between_zero A N, ← between_zero A j, ← between_step A j, between_comp, between_comp]
  rw [hb]
  change (A.toInitial j).base ((A.stepProjection j).base
    ((between A (show j + 1 ≤ N by omega)).base ((finalOldMap A N j h).base z))) = _
  rw [hstep]
  exact centerPoint_toInitial A j

/-- Every point of the newest exceptional fibre projects to the original centre. -/
theorem previousFiber_projection_center (q : ℕ) (z : previousFiber (A.stage q)) :
    (A.toInitial (q + 1)).base ((previousFiberι (A.stage q)).base z) =
      A.chart.base (originPoint (k := k)) := by
  have hz : (previousFiberι (A.stage q)).base z ∈ Set.range (previousFiberι (A.stage q)).base :=
    ⟨z, rfl⟩
  change _ ∈ Set.range (PointBlowupGluing.globalCenterFiberι
    (A.stage q).chart (originPoint (k := k)) (A.stage q).center_closed).base at hz
  rw [PointBlowupGluing.range_globalCenterFiberι] at hz
  have hstep : (A.stepProjection q).base ((previousFiberι (A.stage q)).base z) =
      (A.stage q).chart.base (originPoint (k := k)) := hz
  rw [PlaneChartedScheme.toInitial_succ]
  change (A.toInitial q).base ((A.stepProjection q).base ((previousFiberι (A.stage q)).base z)) = _
  rw [hstep]
  exact centerPoint_toInitial A q

/-- Every point of every final exceptional component projects to the original centre. -/
theorem finalComponent_projection_center (q : ℕ) (idx : FinalIndex.{0} q)
    (z : finalComponent A q idx) :
    (A.toInitial (q + 1)).base ((finalComponentι A q idx).base z) =
      A.chart.base (originPoint (k := k)) := by
  cases idx with
  | inl j => exact finalOldMap_projection_center A (q + 1) j.val (by omega) z
  | inr t => exact previousFiber_projection_center A q z

end Tower

section Complement

/-- The complement of all selected centres other than the `i`-th, as a finite meet of the accepted
centre complements. -/
def otherComplement (q : ℕ) :
    (n : ℕ) → (a : Fin n → k) → Fin n → (projectiveProduct k).Opens
  | 0, _, i => i.elim0
  | m + 1, a, i =>
    Fin.lastCases (motive := fun _ => (projectiveProduct k).Opens)
      (earlierComplement (q + 1) m (fun j => a j.castSucc))
      (fun i' => otherComplement q m (fun j => a j.castSucc) i' ⊓
        initialPuncture (translatedInitial (q + 1) (a (Fin.last m))))
      i

theorem otherComplement_last (q m : ℕ) (a : Fin (m + 1) → k) :
    otherComplement q (m + 1) a (Fin.last m) =
      earlierComplement (q + 1) m (fun j => a j.castSucc) :=
  Fin.lastCases_last

theorem otherComplement_castSucc (q m : ℕ) (a : Fin (m + 1) → k) (i' : Fin m) :
    otherComplement q (m + 1) a i'.castSucc =
      otherComplement q m (fun j => a j.castSucc) i' ⊓
        initialPuncture (translatedInitial (q + 1) (a (Fin.last m))) :=
  Fin.lastCases_castSucc i'

theorem mem_otherComplement_iff (q : ℕ) :
    ∀ (n : ℕ) (a : Fin n → k) (i : Fin n) (x : projectiveProduct k),
      x ∈ otherComplement q n a i ↔ ∀ j, j ≠ i → x ≠ graphPoint (q + 1) (a j)
  | 0, _, i, _ => i.elim0
  | m + 1, a, i, x => by
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · rw [otherComplement_last, mem_earlierComplement_iff, Fin.forall_fin_succ']
        constructor
        · intro h
          exact ⟨fun j _ => h j, fun hne => absurd rfl hne⟩
        · intro h j
          exact h.1 j (Fin.castSucc_ne_last j)
      · rw [otherComplement_castSucc, TopologicalSpace.Opens.mem_inf,
          mem_otherComplement_iff q m, Fin.forall_fin_succ']
        apply and_congr
        · constructor
          · intro h j hj
            exact h j (fun hji => hj (congrArg Fin.castSucc hji))
          · intro h j hj
            exact h j (fun hji => hj (Fin.castSucc_injective m hji))
        · change x ≠ (translatedInitial (q + 1) (a (Fin.last m))).chart.base (originPoint (k := k)) ↔ _
          rw [selected_center]
          exact ⟨fun h _ => h, fun h => h (Fin.castSucc_ne_last i').symm⟩

theorem center_not_mem_otherComplement (q n : ℕ) (a : Fin n → k) (i j : Fin n) (hji : j ≠ i) :
    graphPoint (q + 1) (a j) ∉ otherComplement q n a i := fun h =>
  (mem_otherComplement_iff q n a i _).mp h j hji rfl

theorem center_mem_otherComplement [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) :
    graphPoint (q + 1) (a i) ∈ otherComplement q n a i := by
  rw [mem_otherComplement_iff]
  intro j hji h
  exact hji (ha (graphPoint_injective (q + 1) h)).symm

end Complement

/-- Transport of the restriction-isomorphism property along an equality of opens. -/
theorem isIso_restrict_congr {Y Z : Scheme.{u}} (f : Y ⟶ Z) {U V : Z.Opens} (h : U = V)
    [IsIso (f ∣_ U)] : IsIso (f ∣_ V) := by
  subst h
  infer_instance

/-- The projection of the multi-centre surface onto the `i`-th tower is an isomorphism over any
open avoiding the other centres. -/
theorem towerProjection_restrict_isIso (q : ℕ) :
    ∀ (n : ℕ) (a : Fin n → k) (i : Fin n) (U : (projectiveProduct k).Opens),
      (∀ j, j ≠ i → graphPoint (q + 1) (a j) ∉ U) →
      IsIso (towerProjection (q + 1) n a i ∣_ (selectedProjection (q + 1) (a i) (q + 1) ⁻¹ᵁ U))
  | 0, _, i, _, _ => i.elim0
  | m + 1, a, i, U, hU => by
      revert hU
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · intro hU
        letI hf : IsIso (multiProjection (q + 1) m (fun j => a j.castSucc) ∣_ U) :=
          multiProjection_restrict_isIso (q + 1) m _ U
            (fun j => hU j.castSucc (Fin.castSucc_ne_last j))
        rw [towerProjection_last]
        exact isIso_pullback_snd_restrict _ _ U
      · intro hU
        letI hIH : IsIso (towerProjection (q + 1) m (fun j => a j.castSucc) i' ∣_
            (selectedProjection (q + 1) (a i'.castSucc) (q + 1) ⁻¹ᵁ U)) :=
          towerProjection_restrict_isIso q m _ i' U
            (fun j hj => hU j.castSucc (fun h => hj (Fin.castSucc_injective m h)))
        letI hg : IsIso (selectedProjection (q + 1) (a (Fin.last m)) (q + 1) ∣_ U) :=
          selectedProjection_restrict_isIso (q + 1) _ U
            (hU (Fin.last m) (Fin.castSucc_ne_last i').symm)
        have heq : multiProjection (q + 1) m (fun j => a j.castSucc) ⁻¹ᵁ U =
            towerProjection (q + 1) m (fun j => a j.castSucc) i' ⁻¹ᵁ
              (selectedProjection (q + 1) (a i'.castSucc) (q + 1) ⁻¹ᵁ U) := by
          rw [← Scheme.preimage_comp, towerProjection_projection]
        letI h0 := isIso_pullback_fst_restrict (multiProjection (q + 1) m (fun j => a j.castSucc))
          (selectedProjection (q + 1) (a (Fin.last m)) (q + 1)) U
        letI hfst : IsIso (pullback.fst (multiProjection (q + 1) m (fun j => a j.castSucc))
            (selectedProjection (q + 1) (a (Fin.last m)) (q + 1)) ∣_
              (towerProjection (q + 1) m (fun j => a j.castSucc) i' ⁻¹ᵁ
                (selectedProjection (q + 1) (a i'.castSucc) (q + 1) ⁻¹ᵁ U))) :=
          isIso_restrict_congr _ heq
        rw [towerProjection_castSucc, morphismRestrict_comp]
        infer_instance

section Curves

variable (q n : ℕ) (a : Fin n → k)

/-- The exceptional curve `E_{i,idx}` of `S_{p,n}`: the base change to `S_{p,n}` of the accepted
final exceptional component `idx` of the `i`-th tower. -/
def exceptionalCurve (i : Fin n) (idx : FinalIndex.{0} q) : Scheme.{u} :=
  pullback (towerProjection (q + 1) n a i)
    (finalComponentι (translatedInitial (q + 1) (a i)) q idx)

/-- Its closed immersion into `S_{p,n}`. -/
def exceptionalCurveι (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalCurve q n a i idx ⟶ multiSurface (q + 1) n a :=
  pullback.fst _ _

/-- Its comparison map to the accepted component of the tower. -/
def exceptionalCurveToComponent (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalCurve q n a i idx ⟶ finalComponent (translatedInitial (q + 1) (a i)) q idx :=
  pullback.snd _ _

instance exceptionalCurveι_isClosedImmersion (i : Fin n) (idx : FinalIndex.{0} q) :
    IsClosedImmersion (exceptionalCurveι q n a i idx) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

@[reassoc] theorem exceptionalCurve_condition (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalCurveι q n a i idx ≫ towerProjection (q + 1) n a i =
      exceptionalCurveToComponent q n a i idx ≫
        finalComponentι (translatedInitial (q + 1) (a i)) q idx :=
  pullback.condition

/-- The support of `E_{i,idx}` in `S_{p,n}`. -/
def exceptionalSupport (i : Fin n) (idx : FinalIndex.{0} q) : Set (multiSurface (q + 1) n a) :=
  Set.range (exceptionalCurveι q n a i idx).base

theorem exceptionalSupport_eq (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalSupport q n a i idx =
      (towerProjection (q + 1) n a i).base ⁻¹'
        finalSupport (translatedInitial (q + 1) (a i)) q idx :=
  Scheme.Pullback.range_fst _ _

theorem exceptionalSupport_isClosed (i : Fin n) (idx : FinalIndex.{0} q) :
    IsClosed (exceptionalSupport q n a i idx) :=
  (exceptionalCurveι q n a i idx).isClosedEmbedding.isClosed_range

/-- Every point of `E_{i,idx}` projects to the `i`-th selected centre. -/
theorem exceptionalSupport_projection (i : Fin n) (idx : FinalIndex.{0} q)
    (x : multiSurface (q + 1) n a) (hx : x ∈ exceptionalSupport q n a i idx) :
    (multiProjection (q + 1) n a).base x = graphPoint (q + 1) (a i) := by
  rw [exceptionalSupport_eq] at hx
  obtain ⟨z, hz⟩ := hx
  rw [← towerProjection_projection (q + 1) n a i]
  change (selectedProjection (q + 1) (a i) (q + 1)).base
    ((towerProjection (q + 1) n a i).base x) = _
  rw [← hz]
  exact (finalComponent_projection_center (translatedInitial (q + 1) (a i)) q idx z).trans
    (selected_center (q + 1) (a i))

/-- Exceptional curves of different towers are disjoint. -/
theorem exceptionalSupport_disjoint_of_ne [IsAlgClosed k] (ha : Function.Injective a)
    {i i' : Fin n} (hii' : i ≠ i') (idx idx' : FinalIndex.{0} q) :
    Disjoint (exceptionalSupport q n a i idx) (exceptionalSupport q n a i' idx') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := exceptionalSupport_projection q n a i idx x hx
  have h2 := exceptionalSupport_projection q n a i' idx' x hx'
  exact hii' (ha (graphPoint_injective (q + 1) (h1.symm.trans h2)))

/-- Non-adjacent exceptional curves of one tower are disjoint. -/
theorem exceptionalSupport_disjoint_nonadjacent (i : Fin n) (j j' : Fin q)
    (hjj' : j.val + 1 < j'.val) :
    Disjoint (exceptionalSupport q n a i (Sum.inl j)) (exceptionalSupport q n a i (Sum.inl j')) := by
  rw [exceptionalSupport_eq, exceptionalSupport_eq]
  exact Disjoint.preimage _ (finalSupport_nonadjacent _ q j j' hjj')

/-- `P_i` is disjoint from every `C_{ij}` created two or more blowups earlier. -/
theorem exceptionalSupport_disjoint_newest (i : Fin n) (j : Fin q) (hj : j.val + 1 < q) :
    Disjoint (exceptionalSupport q n a i (Sum.inl j))
      (exceptionalSupport q n a i (Sum.inr PUnit.unit)) := by
  rw [exceptionalSupport_eq, exceptionalSupport_eq]
  exact Disjoint.preimage _ (finalSupport_nonadjacent_newest _ q j hj)

variable [IsAlgClosed k] (ha : Function.Injective a)
include ha

/-- Every exceptional component of the `i`-th tower lies over the complement of the other
centres. -/
theorem finalComponent_mem_otherComplement (i : Fin n) (idx : FinalIndex.{0} q)
    (z : finalComponent (translatedInitial (q + 1) (a i)) q idx) :
    (finalComponentι (translatedInitial (q + 1) (a i)) q idx).base z ∈
      selectedProjection (q + 1) (a i) (q + 1) ⁻¹ᵁ otherComplement q n a i := by
  change (selectedProjection (q + 1) (a i) (q + 1)).base
    ((finalComponentι (translatedInitial (q + 1) (a i)) q idx).base z) ∈ otherComplement q n a i
  have h : (selectedProjection (q + 1) (a i) (q + 1)).base
      ((finalComponentι (translatedInitial (q + 1) (a i)) q idx).base z) =
        graphPoint (q + 1) (a i) :=
    (finalComponent_projection_center (translatedInitial (q + 1) (a i)) q idx z).trans
      (selected_center (q + 1) (a i))
  rw [h]
  exact center_mem_otherComplement q n a ha i

theorem finalComponent_range_subset (i : Fin n) (idx : FinalIndex.{0} q) :
    Set.range (finalComponentι (translatedInitial (q + 1) (a i)) q idx).base ⊆
      Set.range (selectedProjection (q + 1) (a i) (q + 1) ⁻¹ᵁ otherComplement q n a i).ι.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨_, finalComponent_mem_otherComplement q n a ha i idx z⟩, rfl⟩

/-- The comparison map of `E_{i,idx}` with the accepted tower component is an isomorphism. -/
theorem exceptionalCurveToComponent_isIso (i : Fin n) (idx : FinalIndex.{0} q) :
    IsIso (exceptionalCurveToComponent q n a i idx) := by
  letI := towerProjection_restrict_isIso q n a i (otherComplement q n a i)
    (fun j hj => center_not_mem_otherComplement q n a i j hj)
  exact isIso_pullback_snd_of_range_subset _ _ _ (finalComponent_range_subset q n a ha i idx)

/-- `E_{i,idx}` is isomorphic to the accepted component of the `i`-th tower. -/
def exceptionalCurveIso (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalCurve q n a i idx ≅ finalComponent (translatedInitial (q + 1) (a i)) q idx := by
  letI := exceptionalCurveToComponent_isIso q n a ha i idx
  exact asIso (exceptionalCurveToComponent q n a i idx)

/-- `P_i = E_{ip}` is isomorphic to the projective line. -/
def newestCurveIso (i : Fin n) :
    exceptionalCurve q n a i (Sum.inr PUnit.unit) ≅ projectiveSpace k 1 :=
  exceptionalCurveIso q n a ha i (Sum.inr PUnit.unit) ≪≫
    previousFiberIso ((translatedInitial (q + 1) (a i)).stage q)

/-- `P_i` is an integral curve. -/
theorem newestCurve_isIntegral (i : Fin n) :
    IsIntegral (exceptionalCurve q n a i (Sum.inr PUnit.unit)) := by
  letI : IsIntegral (finalComponent (translatedInitial (q + 1) (a i)) q (Sum.inr PUnit.unit)) :=
    previousFiber_isIntegral ((translatedInitial (q + 1) (a i)).stage q)
  letI : Nonempty (exceptionalCurve q n a i (Sum.inr PUnit.unit)) :=
    ⟨(exceptionalCurveIso q n a ha i (Sum.inr PUnit.unit)).inv.base
      (Nonempty.some (previousFiber_nonempty ((translatedInitial (q + 1) (a i)).stage q)))⟩
  exact isIntegral_of_isOpenImmersion (exceptionalCurveIso q n a ha i (Sum.inr PUnit.unit)).hom

/-- Each `C_{ij}` is a reduced curve (isomorphic to the accepted strict transform). -/
theorem olderCurve_isReduced (i : Fin n) (j : Fin q) :
    IsReduced (exceptionalCurve q n a i (Sum.inl j)) := by
  letI : IsReduced (finalComponent (translatedInitial (q + 1) (a i)) q (Sum.inl j)) :=
    previousStrictTransform_isReduced ((translatedInitial (q + 1) (a i)).stage j.val)
  exact isReduced_of_isOpenImmersion (exceptionalCurveIso q n a ha i (Sum.inl j)).hom

/-- Adjacent exceptional curves `C_{i,j+1}`, `C_{i,j+2}` of one tower meet in `S_{p,n}`. -/
theorem exceptionalSupport_adjacent (i : Fin n) (j : ℕ) (hj : j + 1 < q) :
    (exceptionalSupport q n a i (Sum.inl ⟨j, by omega⟩) ∩
      exceptionalSupport q n a i (Sum.inl ⟨j + 1, hj⟩)).Nonempty := by
  obtain ⟨y, hy1, hy2⟩ := finalSupport_adjacent (translatedInitial (q + 1) (a i)) q j hj
  obtain ⟨z, rfl⟩ := hy1
  letI := towerProjection_restrict_isIso q n a i (otherComplement q n a i)
    (fun j hj => center_not_mem_otherComplement q n a i j hj)
  obtain ⟨x, hx⟩ := subset_range_of_restrict_isIso (towerProjection (q + 1) n a i)
    (selectedProjection (q + 1) (a i) (q + 1) ⁻¹ᵁ otherComplement q n a i)
    (finalComponent_mem_otherComplement q n a ha i (Sum.inl ⟨j, by omega⟩) z)
  refine ⟨x, ?_, ?_⟩
  · rw [exceptionalSupport_eq, Set.mem_preimage, hx]
    exact ⟨z, rfl⟩
  · rw [exceptionalSupport_eq, Set.mem_preimage, hx]
    exact hy2

end Curves

/-- The last `C_{i,q}` meets `P_i` in `S_{p,n}` (here `p = m + 2`, `q = m + 1`). -/
theorem exceptionalSupport_last_adjacent [IsAlgClosed k] (m n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) :
    (exceptionalSupport (m + 1) n a i (Sum.inl ⟨m, by omega⟩) ∩
      exceptionalSupport (m + 1) n a i (Sum.inr PUnit.unit)).Nonempty := by
  obtain ⟨y, hy1, hy2⟩ := finalSupport_last_adjacent (translatedInitial (m + 1 + 1) (a i)) m
  obtain ⟨z, rfl⟩ := hy1
  letI := towerProjection_restrict_isIso (m + 1) n a i (otherComplement (m + 1) n a i)
    (fun j hj => center_not_mem_otherComplement (m + 1) n a i j hj)
  obtain ⟨x, hx⟩ := subset_range_of_restrict_isIso (towerProjection (m + 1 + 1) n a i)
    (selectedProjection (m + 1 + 1) (a i) (m + 1 + 1) ⁻¹ᵁ otherComplement (m + 1) n a i)
    (finalComponent_mem_otherComplement (m + 1) n a ha i (Sum.inl ⟨m, by omega⟩) z)
  refine ⟨x, ?_, ?_⟩
  · rw [exceptionalSupport_eq, Set.mem_preimage, hx]
    exact ⟨z, rfl⟩
  · rw [exceptionalSupport_eq, Set.mem_preimage, hx]
    exact hy2

end KltDP.Examples.FrobeniusMultiCentreExceptional
