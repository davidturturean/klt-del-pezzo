import KltDP.Examples.FrobeniusExceptionalChainPicard
import KltDP.Examples.FrobeniusSecondChartCrossing

/-!
# Adjacent exceptional curves of a contact tower meet transversally in one point

BRIEF20 (lane F), for an arbitrary charted plane `A : PlaneChartedScheme k` and every `q`.

* **`chainSinglePoints A q : ChainSinglePoints q A`** (lane A1's hypothesis, unconditional): adjacent
  final exceptional components of stage `q+1` meet in at most one point. For the last pair `C_q ∩ P`
  this is the birth-stage statement `strict_inter_fiber_subsingleton` of
  `FrobeniusSecondChartCrossing` (the intersection is the origin of the second Rees chart); for an
  older pair `C_j ∩ C_{j+1}` (`j + 3 ≤ q + 1`) the two components are pulled back from stage `j+2`
  along the accepted projection `between`, which maps their common points into `C_j ∩ P` of stage
  `j+2` (accepted `finalOldMap_projection`, `finalOldMap_projection_mem_fiber`), a single point, and is
  injective on `C_j` (`old_pair_subsingleton`).
* The exceptional locus `X = chainScheme q A` is the glued closed subscheme of the vanishing ideal of the
  union of the components; that ideal sheaf is `⨅ idx, (finalComponentι A q idx).ker.radical`
  (`chainIdeal_eq_iInf`, generic `vanishingIdeal_eq_iInf_ker_radical`), so its ideal on an affine open
  is the infimum of the radicals of the kernel ideals of the components (`chainIdeal_ideal_eq`).
* **Transversality of the last pair** (`transversalCrossing_last`): at the point `x ∈ C_q ∩ P` of
  `X`, `O_{A_{q+1}, x}` is regular of dimension two, the germs of the chart sections `u/v`, `v` of the
  second Rees chart generate its maximal ideal, the kernel of the stalk map of the inclusion of `X` is
  `(u/v · v)` (on the chart the vanishing ideal is `(u/v) ⊓ (v) = (u/v · v)`, all other components
  missing the chart), and the two germs lie in the stalk ideals of the two components
  (`transversalCrossing_of_chart`, `stalkMap_germ_mem_chartIdeal`). This is lane A1's
  `TransversalCrossing (chainInclusion q A) C D x` for the last pair; hence **`chainTransversal_one :
  ChainTransversal 1 A _`** for the two-component chain `C_1 ∪ P`.

Not proved here: the transversal crossing of an older pair `C_j ∩ C_{j+1}` (`j + 1 < q`) on stage `q+1`;
the route (transport of the birth-stage chart along the isomorphism locus of `between`, with the
generic `ker_ideal_map_eq_of_isPullback`) is recorded in `F29_CHAIN_TRANSVERSAL.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace KltDP.Examples.FrobeniusExceptionalChainTransversal

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusGlobalExceptionalSuccessor FrobeniusExceptionalChainPicard FrobeniusSecondChartCrossing
  FrobeniusExceptionalSuccessorChart FrobeniusBlowupChartIteration

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

local instance chainTransversalOriginPoint_isMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## Single points -/

/-- An older adjacent pair `C_j ∩ C_{j+1}` on a stage `N ≥ j + 3` has at most one point. -/
theorem old_pair_subsingleton (N j : ℕ) (h : j + 3 ≤ N) :
    (Set.range (finalOldMap A N j (by omega)).base ∩
      Set.range (finalOldMap A N (j + 1) h).base).Subsingleton := by
  have key : ∀ z : previousStrictTransform (A.stage j),
      (finalOldMap A N j (by omega)).base z ∈ Set.range (finalOldMap A N (j + 1) h).base →
        (previousStrictι (A.stage j)).base z = crossingPoint (A.stage (j + 1)) := by
    intro z hz
    obtain ⟨z', hz'⟩ := hz
    have h2 := finalOldMap_projection_mem_fiber A N (j + 1) h z'
    have e : (between A (show j + 1 + 1 ≤ N by omega)).base ((finalOldMap A N (j + 1) h).base z') =
        (previousStrictι (A.stage j)).base z := by
      rw [hz']
      exact congrArg (fun f => f.base z) (finalOldMap_projection A N j (by omega))
    rw [e] at h2
    exact eq_crossingPoint_of_mem (A.stage j) _ ⟨z, rfl⟩ h2
  rintro x ⟨⟨z, rfl⟩, hx⟩ y ⟨⟨w, rfl⟩, hy⟩
  have hzw := (previousStrictι (A.stage j)).isClosedEmbedding.injective
    ((key z hx).trans (key w hy).symm)
  rw [hzw]

/-- **Lane A1's hypothesis `ChainSinglePoints`, for every charted plane and every `q`.** -/
theorem chainSinglePoints (q : ℕ) : ChainSinglePoints q A where
  old j hj := by
    show (Set.range (finalOldMap A (q + 1) j (by omega)).base ∩
      Set.range (finalOldMap A (q + 1) (j + 1) (by omega)).base).Subsingleton
    exact old_pair_subsingleton A (q + 1) j (by omega)
  newest m hq := by
    subst hq
    show (Set.range (finalOldMap A (m + 2) m (le_refl _)).base ∩
      Set.range (previousFiberι (A.stage (m + 1))).base).Subsingleton
    rw [finalOldMap_birth]
    exact strict_inter_fiber_subsingleton (A.stage m)

/-! ## The vanishing ideal of the exceptional locus on an affine open -/

theorem chainIdeal_eq_iInf (q : ℕ) :
    chainIdeal q A = ⨅ idx : FinalIndex.{u} q, (finalComponentι A q idx).ker.radical :=
  Scheme.IdealSheafData.vanishingIdeal_eq_iInf_ker_radical (finalComponentι A q)
    ⟨chainLocus q A, chainLocus_isClosed q A⟩ rfl

theorem chainIdeal_ideal_eq (q : ℕ) (U : (chainStage q A).affineOpens) :
    (chainIdeal q A).ideal U =
      ⨅ idx : FinalIndex.{u} q, ((finalComponentι A q idx).ker.ideal U).radical := by
  rw [chainIdeal_eq_iInf, Scheme.IdealSheafData.ideal_iInf, iInf_apply]
  simp only [Scheme.IdealSheafData.radical_ideal]

/-! ## The transversal crossing from a chart -/

section Configuration

variable (q : ℕ) [NoetherianSpace (chainStage q A)] [IsLocallyNoetherian (chainStage q A)]

omit [IsLocallyNoetherian (chainStage q A)] in
/-- A germ of a section vanishing on a component lies in the stalk ideal of that component of the
exceptional locus. -/
theorem stalkMap_germ_mem_chartIdeal (hyp : ChainSinglePoints q A) (i : Fin (q + 1))
    (x : chainScheme q A) (U : (chainStage q A).affineOpens)
    (hxU : (chainInclusion q A).base x ∈ U.1) (s : Γ(chainStage q A, U.1))
    (hs : s ∈ (finalComponentι A q (chainMember.{u} q i)).ker.ideal U) :
    (chainInclusion q A).stalkMap x ((chainStage q A).presheaf.germ U.1 _ hxU s) ∈
      (componentChartIdeal (chainScheme q A) {chainComponentEquiv q A hyp i}
        ⟨chainInclusion q A ⁻¹ᵁ U.1, U.2.preimage (chainInclusion q A)⟩).map
          ((chainScheme q A).presheaf.germ (chainInclusion q A ⁻¹ᵁ U.1) x hxU).hom := by
  rw [Scheme.stalkMap_germ_apply]
  apply Ideal.mem_map_of_mem
  have hle : (chainCurve q A (chainMember.{u} q i)).ker ≤
      componentUnionIdeal (chainScheme q A) {chainComponentEquiv q A hyp i} := by
    rw [componentUnionIdeal, ← Scheme.IdealSheafData.subset_support_iff_le_vanishingIdeal,
      coe_componentClosedUnion_singleton, chainComponentEquiv_val]
    exact (chainCurve q A (chainMember.{u} q i)).range_subset_ker_support
  show (chainInclusion q A).app U.1 s ∈
    (componentUnionIdeal (chainScheme q A) {chainComponentEquiv q A hyp i}).ideal
      ⟨chainInclusion q A ⁻¹ᵁ U.1, U.2.preimage (chainInclusion q A)⟩
  refine (Scheme.IdealSheafData.le_def.mp hle)
    ⟨chainInclusion q A ⁻¹ᵁ U.1, U.2.preimage (chainInclusion q A)⟩ ?_
  have hmem : s ∈ (chainCurve q A (chainMember.{u} q i) ≫ chainInclusion q A).ker.ideal U := by
    rw [chainCurve_comp]
    exact Scheme.IdealSheafData.le_def.mp
      (Scheme.Hom.le_ker_comp (chainCurveIso q A (chainMember.{u} q i)).inv
        (finalComponentι A q (chainMember.{u} q i))) U hs
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hmem
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have e1 := ConcreteCategory.congr_hom
    (Scheme.comp_app (chainCurve q A (chainMember.{u} q i)) (chainInclusion q A) U.1) s
  exact e1.symm.trans hmem

omit [IsLocallyNoetherian (chainStage q A)] in
/-- Transversal crossing of two components of the exceptional locus from chart data: an affine open
`U` of the stage through the point, a regular two-dimensional stalk, two sections of `U` whose germs
generate the maximal ideal, such that the vanishing ideal of the locus on `U` is generated by their
product and each section vanishes on its component. -/
theorem transversalCrossing_of_chart (hyp : ChainSinglePoints q A) (i i' : Fin (q + 1))
    (x : chainScheme q A) (U : (chainStage q A).affineOpens)
    (hxU : (chainInclusion q A).base x ∈ U.1)
    (hreg : RegularLocal ((chainStage q A).presheaf.stalk ((chainInclusion q A).base x)))
    (hdim : ringKrullDim ((chainStage q A).presheaf.stalk ((chainInclusion q A).base x)) = 2)
    (sU sV : Γ(chainStage q A, U.1))
    (hspan : Ideal.span {(chainStage q A).presheaf.germ U.1 _ hxU sU,
      (chainStage q A).presheaf.germ U.1 _ hxU sV} =
      maximalIdeal ((chainStage q A).presheaf.stalk ((chainInclusion q A).base x)))
    (hker : (chainIdeal q A).ideal U = Ideal.span {sU * sV})
    (hsU : sU ∈ (finalComponentι A q (chainMember.{u} q i)).ker.ideal U)
    (hsV : sV ∈ (finalComponentι A q (chainMember.{u} q i')).ker.ideal U) :
    TransversalCrossing (chainInclusion q A) (chainComponentEquiv q A hyp i)
      (chainComponentEquiv q A hyp i') x := by
  refine TransversalCrossing.ofChart (chainInclusion q A) _ _ x hreg hdim
    ((chainStage q A).presheaf.germ U.1 _ hxU sU) ((chainStage q A).presheaf.germ U.1 _ hxU sV)
    hspan ?_ ⟨chainInclusion q A ⁻¹ᵁ U.1, U.2.preimage (chainInclusion q A)⟩ hxU
    (stalkMap_germ_mem_chartIdeal A q hyp i x U hxU sU hsU)
    (stalkMap_germ_mem_chartIdeal A q hyp i' x U hxU sV hsV)
  change RingHom.ker ((chainIdeal q A).gluedTo.stalkMap x).hom = _
  rw [Scheme.IdealSheafData.stalkMap_gluedTo_ker_eq_map (chainIdeal q A) U hxU, hker,
    Ideal.map_span, Set.image_singleton, map_mul]
  rfl

end Configuration

/-! ## The last pair `C_q ∩ P` on its birth stage -/

/-- The older components `C_i`, `i + 2 ≤ m + 1`, miss the second Rees chart of stage `m+2`. -/
theorem old_not_mem_secondOpen (m i : ℕ) (hi : i + 2 ≤ m + 1) (z : previousStrictTransform (A.stage i)) :
    (finalOldMap A (m + 2) i (by omega)).base z ∉ (secondOpen (A.stage (m + 1))).1 := by
  intro hz
  have hz' : (finalOldMap A (m + 2) i (by omega)).base z ∈
      (secondChart (A.stage (m + 1))).opensRange := by
    rw [← Scheme.Hom.image_top_eq_opensRange]
    exact hz
  obtain ⟨p, hp⟩ := hz'
  apply finalOldMap_avoids_chart A (m + 1) i hi z
  have hb : between A (show m + 1 ≤ m + 2 by omega) = A.stepProjection (m + 1) :=
    between_step A (m + 1)
  have h1 : (A.stepProjection (m + 1)).base ((finalOldMap A (m + 2) i (by omega)).base z) =
      (finalOldMap A (m + 1) i hi).base z := by
    have h := congrArg (fun f => f.base z) (finalOldMap_between A hi (show m + 1 ≤ m + 2 by omega))
    rw [hb] at h
    exact h
  rw [← h1, ← hp]
  refine ⟨(Spec.map (CommRingCat.ofHom
    (KltDP.Geometry.AffineBlowup.chartBaseMap (FrobeniusBlowupContact.centerIdeal (k := k))
      FrobeniusBlowupContact.centerV))).base p, ?_⟩
  exact (congrArg (fun f => f.base p) (secondChart_projection (A.stage (m + 1)))).symm

/-- The last older component of stage `m+2` is the strict transform `previousStrictι (A.stage m)`. -/
theorem finalComponentι_last (m : ℕ) :
    finalComponentι A (m + 1) (Sum.inl ⟨m, by omega⟩) = previousStrictι (A.stage m) :=
  finalOldMap_birth A m

/-- The second Rees chart open of stage `m+2`, as an affine open of the final stage. -/
def birthOpen (m : ℕ) : (chainStage (m + 1) A).affineOpens := secondOpen (A.stage (m + 1))

theorem birthOpen_strict_ideal (m : ℕ) :
    (previousStrictι (A.stage m)).ker.ideal (birthOpen A m) =
      Ideal.span {(secondSections (A.stage (m + 1))).symm oldRatio} :=
  eq_span_symm_of_map_eq _ (strict_ideal_secondOpen (A.stage m))

theorem birthOpen_fiber_ideal (m : ℕ) :
    (previousFiberι (A.stage (m + 1))).ker.ideal (birthOpen A m) =
      Ideal.span {(secondSections (A.stage (m + 1))).symm vEquation} :=
  eq_span_symm_of_map_eq _ (fiber_ideal_secondOpen (A.stage (m + 1)))

/-- On the second Rees chart of stage `m+2`, the vanishing ideal of the exceptional locus is
`(u/v · v)`: the ideal of `C_m` is `(u/v)`, the ideal of `P` is `(v)`, the older components miss the
chart. -/
theorem chainIdeal_secondOpen (m : ℕ) :
    (chainIdeal (m + 1) A).ideal (birthOpen A m) =
      Ideal.span {(secondSections (A.stage (m + 1))).symm oldRatio *
        (secondSections (A.stage (m + 1))).symm vEquation} := by
  rw [chainIdeal_ideal_eq,
    iInf_eq_inf_of_top _ (Sum.inl ⟨m, by omega⟩ : FinalIndex.{u} (m + 1)) (Sum.inr PUnit.unit)]
  · have hC : (finalComponentι A (m + 1) (Sum.inl ⟨m, by omega⟩)).ker.ideal (birthOpen A m) =
        Ideal.span {(secondSections (A.stage (m + 1))).symm oldRatio} := by
      rw [finalComponentι_last]
      exact birthOpen_strict_ideal A m
    have hP : (finalComponentι A (m + 1) (Sum.inr PUnit.unit)).ker.ideal (birthOpen A m) =
        Ideal.span {(secondSections (A.stage (m + 1))).symm vEquation} :=
      birthOpen_fiber_ideal A m
    rw [hC, hP, (span_symm_oldRatio_isPrime _).radical, (span_symm_vEquation_isPrime _).radical,
      span_symm_inf,
      map_mul (secondSections (A.stage (m + 1))).symm (oldRatio (k := k)) (vEquation (k := k))]
  · rintro (⟨i, hi⟩ | ⟨⟩) hne hne'
    · have him : i + 2 ≤ m + 1 := by
        rcases Nat.lt_or_ge i m with h | h
        · omega
        · exfalso
          apply hne
          congr 1
          exact Fin.ext (show i = m by omega)
      have hi' : (finalComponentι A (m + 1) (Sum.inl ⟨i, hi⟩)).ker.ideal (birthOpen A m) = ⊤ :=
        ker_ideal_eq_top_of_disjoint _ _ (old_not_mem_secondOpen A m i him)
      rw [hi', Ideal.radical_top]
    · exact absurd rfl hne'

section Last

variable (m : ℕ) [NoetherianSpace (chainStage (m + 1) A)] [IsLocallyNoetherian (chainStage (m + 1) A)]

omit [IsLocallyNoetherian (chainStage (m + 1) A)] in
/-- **The last pair `C_{m+1}`, `P` of the chain of stage `m+2` crosses transversally at its common
point** (lane A1's `TransversalCrossing`). -/
theorem transversalCrossing_last (hyp : ChainSinglePoints (m + 1) A) (j : Fin (m + 1))
    (hj : j.val = m) (x : chainScheme (m + 1) A)
    (hC : x ∈ (chainComponentEquiv (m + 1) A hyp j.castSucc).1)
    (hD : x ∈ (chainComponentEquiv (m + 1) A hyp j.succ).1) :
    TransversalCrossing (chainInclusion (m + 1) A) (chainComponentEquiv (m + 1) A hyp j.castSucc)
      (chainComponentEquiv (m + 1) A hyp j.succ) x := by
  have hmemC : chainMember.{u} (m + 1) j.castSucc = Sum.inl ⟨m, by omega⟩ := by
    rw [chainMember_of_lt (m + 1) j.castSucc (by rw [Fin.coe_castSucc]; omega)]
    congr 1
    exact Fin.ext (by rw [Fin.coe_castSucc]; exact hj)
  have hmemD : chainMember.{u} (m + 1) j.succ = Sum.inr PUnit.unit :=
    chainMember_of_not_lt (m + 1) j.succ (by rw [Fin.val_succ]; omega)
  have hC' : (chainInclusion (m + 1) A).base x ∈
      finalSupport A (m + 1) (chainMember.{u} (m + 1) j.castSucc) := by
    have h := hC
    rw [chainComponentEquiv_val, range_chainCurve_eq] at h
    exact h
  have hD' : (chainInclusion (m + 1) A).base x ∈
      finalSupport A (m + 1) (chainMember.{u} (m + 1) j.succ) := by
    have h := hD
    rw [chainComponentEquiv_val, range_chainCurve_eq] at h
    exact h
  rw [hmemC] at hC'
  rw [hmemD] at hD'
  have hyC : (chainInclusion (m + 1) A).base x ∈ Set.range (previousStrictι (A.stage m)).base := by
    have h : (chainInclusion (m + 1) A).base x ∈
        Set.range (finalOldMap A (m + 2) m (le_refl _)).base := hC'
    rwa [finalOldMap_birth] at h
  have hyD : (chainInclusion (m + 1) A).base x ∈
      Set.range (previousFiberι (A.stage (m + 1))).base := hD'
  have hy : (chainInclusion (m + 1) A).base x = crossingPoint (A.stage (m + 1)) :=
    eq_crossingPoint_of_mem (A.stage m) _ hyC hyD
  refine transversalCrossing_of_chart A (m + 1) hyp j.castSucc j.succ x (birthOpen A m)
    (mem_secondOpen_of_eq _ _ hy) (regularLocal_of_eq _ _ hy) (ringKrullDim_of_eq _ _ hy) _ _
    (span_germs_of_eq _ _ hy) (chainIdeal_secondOpen A m) ?_ ?_
  · rw [hmemC, finalComponentι_last, birthOpen_strict_ideal]
    exact Ideal.mem_span_singleton_self _
  · rw [hmemD]
    show _ ∈ (previousFiberι (A.stage (m + 1))).ker.ideal (birthOpen A m)
    rw [birthOpen_fiber_ideal]
    exact Ideal.mem_span_singleton_self _

end Last

/-- **The two-component chain `C_1 ∪ P` of stage `2` is a transversal chain**: lane A1's
`ChainTransversal 1 A _`. -/
theorem chainTransversal_one [NoetherianSpace (chainStage 1 A)] [IsLocallyNoetherian (chainStage 1 A)] :
    ChainTransversal 1 A (chainSinglePoints A 1) := by
  intro j x hC hD
  exact transversalCrossing_last A 0 (chainSinglePoints A 1) j (by have := j.isLt; omega) x hC hD

/-- Universe check: the single-point hypothesis at universe `0`. -/
example (k₀ : Type) [Field k₀] (A₀ : PlaneChartedScheme k₀) (q₀ : ℕ) : ChainSinglePoints q₀ A₀ :=
  chainSinglePoints A₀ q₀

end KltDP.Examples.FrobeniusExceptionalChainTransversal
