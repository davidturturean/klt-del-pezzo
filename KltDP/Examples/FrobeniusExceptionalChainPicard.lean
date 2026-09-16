import KltDP.Geometry.RationalTreePicardDualGraphTransport
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.PrimeCurveCodimension
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration
import KltDP.Examples.FrobeniusPreviousStrictIsoProjectiveLine

/-!
# The exceptional chain of a contact tower as a rational tree: `Pic ≃* ℤ^{q+1}`

BRIEF19, task 3 (the §10 consumer of `lem:tree-picard`). Let `A` be a charted plane and
`A_{q+1} = (A.stage (q+1)).carrier` the stage after `q+1` blowups of the successive centres. Its
exceptional locus is the union of the `q+1` final exceptional components `C_1, …, C_q, P`
(accepted `finalComponentι A q idx`, `idx : FinalIndex q = Fin q ⊕ PUnit`; `Sum.inl j` is the
strict transform `C_{j+1}` of the `(j+1)`-st exceptional curve, `Sum.inr _` the newest fibre `P`).
This module realises the exceptional locus as the reduced closed subscheme `chainScheme A q` of
`A_{q+1}` (glued subscheme of the vanishing ideal of `⋃ finalSupport`), lifts each component to
a closed immersion `chainCurve A q idx : P¹ ⟶ chainScheme A q` (lane F's
`previousStrictIsoProjectiveLine` for the older curves, the accepted `previousFiberIso` for `P`,
and the lane's `liftGluedTo`), and proves the hypotheses of the configuration corollary
`rationalTreePicard_of_configuration`:

* the curves cover the locus and are pairwise incomparable (`chainCurve_cover`,
  `chainCurve_distinct`);
* the components form a chain (`chain_isChain`): non-adjacent curves are disjoint (accepted
  `finalSupport_nonadjacent`, `finalSupport_nonadjacent_newest`), adjacent curves meet (accepted
  `finalSupport_adjacent`, `finalSupport_last_adjacent`) in **at most one point — this is the
  hypothesis `ChainSinglePoints A q`**, awaited from lane F's `FrobeniusExceptionalChainTransversal`
  (not delivered at the time of writing); hence the incidence graph is a path, a tree
  (`chain_isTree`, through `isTree_of_chain`);
* `topologicalKrullDim ≤ 1` from the curves (`chain_dim`);
* the transversal configuration (`chain_transversalConfiguration`): no triple points and the
  crossings of non-adjacent pairs follow from the chain structure; **the transversality of the
  crossing of adjacent curves is the hypothesis `ChainTransversal A q hyp`** (the second half of
  lane F's pending module: `O_{A_{q+1}, x}` regular of dimension two with local equations of the
  two curves generating the maximal ideal and `O_{X, x} = O_{A_{q+1}, x}/(fg)`).

With `[NoetherianSpace A_{q+1}]`, `[IsLocallyNoetherian A_{q+1}]` and
`[LocallyOfFiniteType (A.stage (q+1)).structureMap]` (not in the accepted tree for the tower
stages; carried as instance hypotheses) and `k` algebraically closed, the multidegree map of the
exceptional locus is bijective (`chain_rationalTreePicard`), so
`Pic(C_1 ∪ ⋯ ∪ C_q ∪ P) ≃* ℤ^{FinalIndex q} ≃* ℤ^{q+1}` (`chainPicardEquiv`,
`chainPicardEquivFin`), and a line bundle of exponent zero on every curve is trivial
(`chain_trivial_of_degree_zero`). A universe check instantiates the statement at `Scheme.{0}`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Geometry.RationalTreePicard

universe u

namespace KltDP.Examples.FrobeniusExceptionalChainPicard

open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusPreviousStrictIsoProjectiveLine FrobeniusGlobalExceptionalSuccessor
  FrobeniusBlowupChartIteration

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

local instance projectiveLine_isIntegral' : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-! ## The projective line -/

theorem projectiveLine_dim_le_one : topologicalKrullDim (projectiveSpace k 1) ≤ 1 := by
  rw [projectiveSpace_topologicalKrullDim, Nat.cast_one]

/-- `P¹` has two distinct points (it has dimension one). -/
theorem projectiveLine_nontrivial : Nontrivial (projectiveSpace k 1) := by
  by_contra hcon
  rw [not_nontrivial_iff_subsingleton] at hcon
  have hd := KltDP.Geometry.topologicalKrullDim_nonpos_of_subsingleton (projectiveSpace k 1)
  rw [projectiveSpace_topologicalKrullDim, Nat.cast_one] at hd
  have hpos : (0 : WithBot ℕ∞) < 1 := WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)
  exact hpos.not_le hd

/-! ## Index bookkeeping: `FinalIndex q ≃ Fin (q+1)` -/

variable (q : ℕ)

/-- The `i`-th member of the chain: `C_{i+1}` for `i < q`, `P` for `i = q`. -/
def chainMember (i : Fin (q + 1)) : FinalIndex.{u} q :=
  if h : i.val < q then Sum.inl ⟨i.val, h⟩ else Sum.inr PUnit.unit

theorem chainMember_of_lt (i : Fin (q + 1)) (h : i.val < q) :
    chainMember.{u} q i = Sum.inl ⟨i.val, h⟩ := dif_pos h

theorem chainMember_of_not_lt (i : Fin (q + 1)) (h : ¬ i.val < q) :
    chainMember.{u} q i = Sum.inr PUnit.unit := dif_neg h

/-- The position of a component in the chain. -/
def chainIndexOf : FinalIndex.{u} q → Fin (q + 1)
  | Sum.inl j => j.castSucc
  | Sum.inr _ => Fin.last q

/-- The chain enumeration of the final exceptional components. -/
def chainEquiv : Fin (q + 1) ≃ FinalIndex.{u} q where
  toFun := chainMember q
  invFun := chainIndexOf q
  left_inv i := by
    by_cases h : i.val < q
    · exact (congrArg (chainIndexOf q) (chainMember_of_lt q i h)).trans (Fin.ext rfl)
    · exact (congrArg (chainIndexOf q) (chainMember_of_not_lt q i h)).trans
        (Fin.ext (show q = i.val by have := i.isLt; omega))
  right_inv idx := by
    rcases idx with j | ⟨⟩
    · exact (chainMember_of_lt q j.castSucc (by rw [Fin.coe_castSucc]; exact j.isLt)).trans rfl
    · exact chainMember_of_not_lt q (Fin.last q) (by rw [Fin.val_last]; exact lt_irrefl q)

/-! ## The exceptional curves of the final stage -/

variable (A : PlaneChartedScheme k)

/-- The final stage `A_{q+1}` of the tower. -/
abbrev chainStage : Scheme.{u} := (A.stage (q + 1)).carrier

/-- **Hypothesis awaited from lane F** (`FrobeniusExceptionalChainTransversal`, BRIEF19):
adjacent exceptional curves of the final stage meet in at most one point (with the accepted
`finalSupport_adjacent`, `finalSupport_last_adjacent`: in exactly one point). -/
structure ChainSinglePoints : Prop where
  old : ∀ (j : ℕ) (hj : j + 1 < q),
    (finalSupport A q (Sum.inl ⟨j, by omega⟩ : FinalIndex.{u} q) ∩
      finalSupport A q (Sum.inl ⟨j + 1, hj⟩ : FinalIndex.{u} q)).Subsingleton
  newest : ∀ (m : ℕ) (hq : q = m + 1),
    (finalSupport A q (Sum.inl ⟨m, by omega⟩ : FinalIndex.{u} q) ∩
      finalSupport A q (Sum.inr PUnit.unit : FinalIndex.{u} q)).Subsingleton

/-- The support of the `i`-th member of the chain in `A_{q+1}`. -/
def chainSupport (i : Fin (q + 1)) : Set (chainStage q A) := finalSupport A q (chainMember.{u} q i)

theorem chainSupport_nonempty_last (m : ℕ) (hq : q = m + 1) :
    (finalSupport A q (Sum.inl ⟨m, by omega⟩ : FinalIndex.{u} q) ∩
      finalSupport A q (Sum.inr PUnit.unit : FinalIndex.{u} q)).Nonempty := by
  subst hq
  exact finalSupport_last_adjacent A m

/-- Adjacent members meet (accepted). -/
theorem chainSupport_nonempty (j : Fin q) :
    (chainSupport q A j.castSucc ∩ chainSupport q A j.succ).Nonempty := by
  unfold chainSupport
  rw [chainMember_of_lt q j.castSucc (by rw [Fin.coe_castSucc]; exact j.isLt)]
  by_cases h : j.val + 1 < q
  · rw [chainMember_of_lt q j.succ (by rw [Fin.val_succ]; exact h)]
    exact finalSupport_adjacent A q j.val h
  · rw [chainMember_of_not_lt q j.succ (by rw [Fin.val_succ]; exact h)]
    exact chainSupport_nonempty_last q A j.val (by have := j.isLt; omega)

/-- Adjacent members meet in at most one point (the hypothesis). -/
theorem chainSupport_subsingleton (hyp : ChainSinglePoints q A) (j : Fin q) :
    (chainSupport q A j.castSucc ∩ chainSupport q A j.succ).Subsingleton := by
  unfold chainSupport
  rw [chainMember_of_lt q j.castSucc (by rw [Fin.coe_castSucc]; exact j.isLt)]
  by_cases h : j.val + 1 < q
  · rw [chainMember_of_lt q j.succ (by rw [Fin.val_succ]; exact h)]
    exact hyp.old j.val h
  · rw [chainMember_of_not_lt q j.succ (by rw [Fin.val_succ]; exact h)]
    exact hyp.newest j.val (by have := j.isLt; omega)

/-- Non-adjacent members are disjoint (accepted). -/
theorem chainSupport_disjoint (i j : Fin (q + 1)) (hij : i.val + 1 < j.val) :
    Disjoint (chainSupport q A i) (chainSupport q A j) := by
  unfold chainSupport
  have hj := j.isLt
  rw [chainMember_of_lt q i (by omega)]
  by_cases h : j.val < q
  · rw [chainMember_of_lt q j h]
    exact finalSupport_nonadjacent A q ⟨i.val, by omega⟩ ⟨j.val, h⟩ hij
  · rw [chainMember_of_not_lt q j h]
    exact finalSupport_nonadjacent_newest A q ⟨i.val, by omega⟩ (show i.val + 1 < q by omega)

/-- Each final exceptional component is a projective line: lane F's
`previousStrictIsoProjectiveLine` for the older curves, the accepted `previousFiberIso` for the
newest fibre. -/
def chainCurveIso : (idx : FinalIndex.{u} q) → (finalComponent A q idx ≅ projectiveSpace k 1)
  | Sum.inl j => previousStrictIsoProjectiveLine (A.stage j.val)
  | Sum.inr _ => previousFiberIso (A.stage q)

instance finalComponent_isReduced (idx : FinalIndex.{u} q) :
    AlgebraicGeometry.IsReduced (finalComponent A q idx) :=
  isReduced_of_isOpenImmersion (chainCurveIso q A idx).hom

theorem chainCurveIso_inv_hom_base (idx : FinalIndex.{u} q) (z : finalComponent A q idx) :
    (chainCurveIso q A idx).inv.base ((chainCurveIso q A idx).hom.base z) = z := by
  rw [← Scheme.comp_base_apply, Iso.hom_inv_id]
  rfl

theorem chainCurveIso_hom_inv_base (idx : FinalIndex.{u} q) (p : projectiveSpace k 1) :
    (chainCurveIso q A idx).hom.base ((chainCurveIso q A idx).inv.base p) = p := by
  rw [← Scheme.comp_base_apply, Iso.inv_hom_id]
  rfl

/-! ## The exceptional locus as a reduced closed subscheme -/

/-- The exceptional locus `C_1 ∪ ⋯ ∪ C_q ∪ P` of the final stage. -/
def chainLocus : Set (chainStage q A) := ⋃ idx : FinalIndex.{u} q, finalSupport A q idx

theorem chainLocus_isClosed : IsClosed (chainLocus q A) :=
  isClosed_iUnion_of_finite fun idx => finalSupport_isClosed A q idx

theorem finalSupport_subset_chainLocus (idx : FinalIndex.{u} q) :
    finalSupport A q idx ⊆ chainLocus q A :=
  Set.subset_iUnion (fun idx : FinalIndex.{u} q => finalSupport A q idx) idx

/-- The vanishing ideal sheaf of the exceptional locus. -/
def chainIdeal : (chainStage q A).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨chainLocus q A, chainLocus_isClosed q A⟩

/-- The exceptional locus as a reduced closed subscheme of `A_{q+1}`. -/
def chainScheme : Scheme.{u} := (chainIdeal q A).glueData.glued

/-- The inclusion of the exceptional locus. -/
def chainInclusion : chainScheme q A ⟶ chainStage q A := (chainIdeal q A).gluedTo

instance chainInclusion_isClosedImmersion : IsClosedImmersion (chainInclusion q A) :=
  (chainIdeal q A).gluedTo_isClosedImmersion

instance chainScheme_isReduced : AlgebraicGeometry.IsReduced (chainScheme q A) :=
  (chainIdeal q A).glued_isReduced
    (Scheme.IdealSheafData.vanishingIdeal_support (I := chainIdeal q A)).symm

theorem range_chainInclusion : Set.range (chainInclusion q A).base = chainLocus q A :=
  (chainIdeal q A).range_gluedTo

theorem chainInclusion_injective : Function.Injective (chainInclusion q A).base :=
  (chainInclusion q A).isClosedEmbedding.injective

theorem finalSupport_subset_range (idx : FinalIndex.{u} q) :
    finalSupport A q idx ⊆ Set.range (chainInclusion q A).base := by
  rw [range_chainInclusion]
  exact finalSupport_subset_chainLocus q A idx

theorem chainIdeal_le_ker (idx : FinalIndex.{u} q) :
    chainIdeal q A ≤ (finalComponentι A q idx).ker := by
  refine le_trans ?_ (vanishingIdeal_le_ker (finalComponentι A q idx)
    ⟨finalSupport A q idx, finalSupport_isClosed A q idx⟩ rfl)
  exact Scheme.IdealSheafData.vanishingIdeal_antimono (finalSupport_subset_chainLocus q A idx)

/-- The lift of a final component into the exceptional locus. -/
def chainLift (idx : FinalIndex.{u} q) : finalComponent A q idx ⟶ chainScheme q A :=
  liftGluedTo (chainIdeal q A) (finalComponentι A q idx) (chainIdeal_le_ker q A idx)

theorem chainLift_comp (idx : FinalIndex.{u} q) :
    chainLift q A idx ≫ chainInclusion q A = finalComponentι A q idx :=
  liftGluedTo_gluedTo _ _ _

instance chainLift_isClosedImmersion (idx : FinalIndex.{u} q) :
    IsClosedImmersion (chainLift q A idx) := by
  haveI : IsClosedImmersion (chainLift q A idx ≫ chainInclusion q A) := by
    rw [chainLift_comp]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (chainInclusion q A)

/-- The curves of the exceptional locus as closed immersions of `P¹`. -/
def chainCurve (idx : FinalIndex.{u} q) : projectiveSpace k 1 ⟶ chainScheme q A :=
  (chainCurveIso q A idx).inv ≫ chainLift q A idx

instance chainCurve_isClosedImmersion (idx : FinalIndex.{u} q) :
    IsClosedImmersion (chainCurve q A idx) := by
  unfold chainCurve
  infer_instance

theorem chainCurve_comp (idx : FinalIndex.{u} q) :
    chainCurve q A idx ≫ chainInclusion q A =
      (chainCurveIso q A idx).inv ≫ finalComponentι A q idx := by
  rw [chainCurve, Category.assoc, chainLift_comp]

/-- The image of a curve in the locus is the preimage of the component's support. -/
theorem range_chainCurve_eq (idx : FinalIndex.{u} q) :
    Set.range (chainCurve q A idx).base = (chainInclusion q A).base ⁻¹' finalSupport A q idx := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    show (chainInclusion q A).base ((chainCurve q A idx).base p) ∈
      Set.range (finalComponentι A q idx).base
    rw [← Scheme.comp_base_apply, chainCurve_comp, Scheme.comp_base_apply]
    exact ⟨_, rfl⟩
  · intro hx
    obtain ⟨z, hz⟩ := (show (chainInclusion q A).base x ∈ Set.range (finalComponentι A q idx).base
      from hx)
    refine ⟨(chainCurveIso q A idx).hom.base z, chainInclusion_injective q A ?_⟩
    rw [← Scheme.comp_base_apply, chainCurve_comp, Scheme.comp_base_apply,
      chainCurveIso_inv_hom_base]
    exact hz

/-- The curves cover the exceptional locus. -/
theorem chainCurve_cover :
    ⋃ idx : FinalIndex.{u} q, Set.range (chainCurve q A idx).base = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (chainInclusion q A).base x ∈ chainLocus q A := by
    rw [← range_chainInclusion]
    exact ⟨x, rfl⟩
  unfold chainLocus at hx
  obtain ⟨idx, hidx⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨idx, ?_⟩
  rw [range_chainCurve_eq]
  exact hidx

/-- No member of the chain is a single point. -/
theorem chainSupport_not_subsingleton (i : Fin (q + 1)) :
    ¬ (chainSupport q A i).Subsingleton := by
  haveI : Nontrivial (projectiveSpace k 1) := projectiveLine_nontrivial (k := k)
  haveI : Nontrivial (finalComponent A q (chainMember.{u} q i)) :=
    (Function.LeftInverse.injective (chainCurveIso_hom_inv_base q A (chainMember.{u} q i))).nontrivial
  intro hs
  obtain ⟨a, b, hab⟩ := exists_pair_ne (finalComponent A q (chainMember.{u} q i))
  have ha : (finalComponentι A q (chainMember.{u} q i)).base a ∈ chainSupport q A i := ⟨a, rfl⟩
  have hb : (finalComponentι A q (chainMember.{u} q i)).base b ∈ chainSupport q A i := ⟨b, rfl⟩
  exact hab ((finalComponentι A q (chainMember.{u} q i)).isClosedEmbedding.injective (hs ha hb))

/-- The curves are pairwise incomparable (given the single-point hypothesis). -/
theorem chainCurve_distinct (hyp : ChainSinglePoints q A) (i j : FinalIndex.{u} q)
    (h : Set.range (chainCurve q A i).base ⊆ Set.range (chainCurve q A j).base) : i = j := by
  have hS : finalSupport A q i ⊆ finalSupport A q j := by
    rw [← Set.image_preimage_eq_of_subset (finalSupport_subset_range q A i),
      ← range_chainCurve_eq q A i]
    calc (chainInclusion q A).base '' Set.range (chainCurve q A i).base
        ⊆ (chainInclusion q A).base '' Set.range (chainCurve q A j).base := Set.image_mono h
      _ = finalSupport A q j := by
        rw [range_chainCurve_eq q A j,
          Set.image_preimage_eq_of_subset (finalSupport_subset_range q A j)]
  have key := chain_not_subset (chainSupport q A) (chainSupport_subsingleton q A hyp)
    (chainSupport_disjoint q A) (chainSupport_not_subsingleton q A)
    ((chainEquiv q).symm i) ((chainEquiv q).symm j) (by
      show finalSupport A q (chainEquiv.{u} q ((chainEquiv.{u} q).symm i)) ⊆
        finalSupport A q (chainEquiv.{u} q ((chainEquiv.{u} q).symm j))
      rw [Equiv.apply_symm_apply (chainEquiv.{u} q) i, Equiv.apply_symm_apply (chainEquiv.{u} q) j]
      exact hS)
  exact (chainEquiv q).symm.injective key

/-! ## The configuration hypotheses -/

section Configuration

variable [NoetherianSpace (chainStage q A)] [IsLocallyNoetherian (chainStage q A)]

instance chainScheme_noetherianSpace : NoetherianSpace (chainScheme q A) :=
  noetherianSpace_of_isClosedImmersion (chainInclusion q A)

instance chainScheme_isLocallyNoetherian : IsLocallyNoetherian (chainScheme q A) :=
  isLocallyNoetherian_of_isClosedImmersion (chainInclusion q A)

/-- The chain enumeration of the irreducible components of the exceptional locus. -/
def chainComponentEquiv (hyp : ChainSinglePoints q A) :
    Fin (q + 1) ≃ ↥(irreducibleComponents (chainScheme q A)) :=
  (chainEquiv q).trans (curveComponentEquiv (chainScheme q A) (fun _ => projectiveSpace k 1)
    (chainCurve q A) (fun _ => projectiveLine_isIntegral) (chainCurve_cover q A)
    (chainCurve_distinct q A hyp))

omit [NoetherianSpace (chainStage q A)] [IsLocallyNoetherian (chainStage q A)] in
theorem chainComponentEquiv_val (hyp : ChainSinglePoints q A) (i : Fin (q + 1)) :
    (chainComponentEquiv q A hyp i).1 = Set.range (chainCurve q A (chainMember.{u} q i)).base := rfl

omit [NoetherianSpace (chainStage q A)] [IsLocallyNoetherian (chainStage q A)] in
/-- The components of the exceptional locus form a chain. -/
theorem chain_isChain (hyp : ChainSinglePoints q A) :
    IsChain (chainScheme q A) (chainComponentEquiv q A hyp) where
  subsingleton j := by
    rw [chainComponentEquiv_val, chainComponentEquiv_val, range_chainCurve_eq, range_chainCurve_eq,
      ← Set.preimage_inter]
    exact (chainSupport_subsingleton q A hyp j).preimage (chainInclusion_injective q A)
  nonempty j := by
    rw [chainComponentEquiv_val, chainComponentEquiv_val, range_chainCurve_eq, range_chainCurve_eq,
      ← Set.preimage_inter]
    exact (chainSupport_nonempty q A j).preimage'
      (Set.inter_subset_left.trans (finalSupport_subset_range q A (chainMember.{u} q j.castSucc)))
  disjoint i j hij := by
    rw [chainComponentEquiv_val, chainComponentEquiv_val, range_chainCurve_eq, range_chainCurve_eq]
    exact (chainSupport_disjoint q A i j hij).preimage (chainInclusion q A).base

omit [NoetherianSpace (chainStage q A)] [IsLocallyNoetherian (chainStage q A)] in
/-- The incidence graph of the exceptional locus is a path, hence a tree. -/
theorem chain_isTree (hyp : ChainSinglePoints q A) :
    (componentPointIncidenceGraph (chainScheme q A)).IsTree :=
  isTree_of_chain (chainScheme q A) (chainComponentEquiv q A hyp) (chain_isChain q A hyp)

omit [NoetherianSpace (chainStage q A)] [IsLocallyNoetherian (chainStage q A)] in
/-- The exceptional locus has dimension at most one. -/
theorem chain_dim : topologicalKrullDim (chainScheme q A) ≤ 1 :=
  topologicalKrullDim_le_one_of_curves (chainScheme q A) (fun _ => projectiveSpace k 1)
    (chainCurve q A) (chainCurve_cover q A) (fun _ => projectiveLine_dim_le_one)

/-- **Hypothesis awaited from lane F**: adjacent curves cross transversally at their common point,
in the stalk form `TransversalCrossing` of BRIEF18 (`O_{A_{q+1}, x}` regular of dimension two, local
equations of the two curves generating its maximal ideal, `O_{X, x} = O_{A_{q+1}, x} ⧸ (f g)`). -/
def ChainTransversal (hyp : ChainSinglePoints q A) : Prop :=
  ∀ (j : Fin q) (x : chainScheme q A), x ∈ (chainComponentEquiv q A hyp j.castSucc).1 →
    x ∈ (chainComponentEquiv q A hyp j.succ).1 →
    TransversalCrossing (chainInclusion q A) (chainComponentEquiv q A hyp j.castSucc)
      (chainComponentEquiv q A hyp j.succ) x

omit [IsLocallyNoetherian (chainStage q A)] in
/-- The exceptional locus is a transversal configuration in `A_{q+1}`. -/
theorem chain_transversalConfiguration (hyp : ChainSinglePoints q A)
    (htrans : ChainTransversal q A hyp) : TransversalConfiguration (chainInclusion q A) where
  no_triple C D E x hC hD hE := by
    set e := chainComponentEquiv q A hyp with he
    have key : ∀ a b : Fin (q + 1), a.val + 1 < b.val → x ∈ (e a).1 → x ∈ (e b).1 → False :=
      fun a b hab ha hb => Set.disjoint_left.mp ((chain_isChain q A hyp).disjoint a b hab) ha hb
    have hC' : x ∈ (e (e.symm C)).1 := by rw [Equiv.apply_symm_apply]; exact hC
    have hD' : x ∈ (e (e.symm D)).1 := by rw [Equiv.apply_symm_apply]; exact hD
    have hE' : x ∈ (e (e.symm E)).1 := by rw [Equiv.apply_symm_apply]; exact hE
    by_contra hcon
    push_neg at hcon
    obtain ⟨hCD, hCE, hDE⟩ := hcon
    have hab : (e.symm C).val ≠ (e.symm D).val := fun h => hCD (e.symm.injective (Fin.ext h))
    have hac : (e.symm C).val ≠ (e.symm E).val := fun h => hCE (e.symm.injective (Fin.ext h))
    have hbc : (e.symm D).val ≠ (e.symm E).val := fun h => hDE (e.symm.injective (Fin.ext h))
    rcases (show (e.symm C).val + 1 < (e.symm D).val ∨ (e.symm D).val + 1 < (e.symm C).val ∨
        (e.symm C).val + 1 < (e.symm E).val ∨ (e.symm E).val + 1 < (e.symm C).val ∨
        (e.symm D).val + 1 < (e.symm E).val ∨ (e.symm E).val + 1 < (e.symm D).val by omega)
      with h | h | h | h | h | h
    · exact key _ _ h hC' hD'
    · exact key _ _ h hD' hC'
    · exact key _ _ h hC' hE'
    · exact key _ _ h hE' hC'
    · exact key _ _ h hD' hE'
    · exact key _ _ h hE' hD'
  crossing C D hCD x hC hD := by
    set e := chainComponentEquiv q A hyp with he
    have key : ∀ a b : Fin (q + 1), a.val + 1 < b.val → x ∈ (e a).1 → x ∈ (e b).1 → False :=
      fun a b hab ha hb => Set.disjoint_left.mp ((chain_isChain q A hyp).disjoint a b hab) ha hb
    have hC' : x ∈ (e (e.symm C)).1 := by rw [Equiv.apply_symm_apply]; exact hC
    have hD' : x ∈ (e (e.symm D)).1 := by rw [Equiv.apply_symm_apply]; exact hD
    have hab : (e.symm C).val ≠ (e.symm D).val := fun h => hCD (e.symm.injective (Fin.ext h))
    have hCe : C = e (e.symm C) := (e.apply_symm_apply C).symm
    have hDe : D = e (e.symm D) := (e.apply_symm_apply D).symm
    by_cases h1 : (e.symm C).val + 1 < (e.symm D).val
    · exact (key _ _ h1 hC' hD').elim
    by_cases h2 : (e.symm D).val + 1 < (e.symm C).val
    · exact (key _ _ h2 hD' hC').elim
    rcases (show (e.symm D).val = (e.symm C).val + 1 ∨ (e.symm C).val = (e.symm D).val + 1 by omega)
      with h | h
    · have hj : (e.symm C).val < q := by have := (e.symm D).isLt; omega
      have ha : e.symm C = Fin.castSucc ⟨(e.symm C).val, hj⟩ := Fin.ext rfl
      have hb : e.symm D = Fin.succ ⟨(e.symm C).val, hj⟩ := Fin.ext h
      rw [hCe, hDe, ha, hb]
      exact htrans ⟨(e.symm C).val, hj⟩ x (by rw [← ha]; exact hC') (by rw [← hb]; exact hD')
    · have hj : (e.symm D).val < q := by have := (e.symm C).isLt; omega
      have ha : e.symm D = Fin.castSucc ⟨(e.symm D).val, hj⟩ := Fin.ext rfl
      have hb : e.symm C = Fin.succ ⟨(e.symm D).val, hj⟩ := Fin.ext h
      rw [hCe, hDe, ha, hb]
      exact (htrans ⟨(e.symm D).val, hj⟩ x (by rw [← ha]; exact hD') (by rw [← hb]; exact hC')).symm

end Configuration

/-! ## The Picard group of the exceptional locus -/

section Picard

variable [IsAlgClosed k] [NoetherianSpace (chainStage q A)] [IsLocallyNoetherian (chainStage q A)]
  [LocallyOfFiniteType (A.stage (q + 1)).structureMap]
  (hyp : ChainSinglePoints q A) (htrans : ChainTransversal q A hyp)

include htrans in
/-- **The multidegree map of the exceptional chain is bijective** (Lemma 2.2 for the exceptional
locus `C_1 ∪ ⋯ ∪ C_q ∪ P` of a contact tower, modulo lane F's chain transversality). -/
theorem chain_rationalTreePicard :
    Function.Bijective (multidegreeHom k (chainScheme q A)
      (lineIdentification (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
        (chainCurve_distinct q A hyp))) :=
  rationalTreePicard_of_configuration (chainScheme q A) (chainInclusion q A)
    (A.stage (q + 1)).structureMap (chain_transversalConfiguration q A hyp htrans) (chain_dim q A)
    (chain_isTree q A hyp) (chainCurve q A) (chainCurve_cover q A) (chainCurve_distinct q A hyp)

/-- `Pic(C_1 ∪ ⋯ ∪ C_q ∪ P) ≃* ℤ^{FinalIndex q}`. -/
def chainPicardEquiv : (chainScheme q A).Pic ≃* (FinalIndex.{u} q → Multiplicative ℤ) :=
  picardEquiv_of_configuration (chainScheme q A) (chainInclusion q A)
    (A.stage (q + 1)).structureMap (chain_transversalConfiguration q A hyp htrans) (chain_dim q A)
    (chain_isTree q A hyp) (chainCurve q A) (chainCurve_cover q A) (chainCurve_distinct q A hyp)

/-- `Pic(C_1 ∪ ⋯ ∪ C_q ∪ P) ≃* ℤ^{q+1}`, indexed along the chain. -/
def chainPicardEquivFin : (chainScheme q A).Pic ≃* (Fin (q + 1) → Multiplicative ℤ) :=
  (chainPicardEquiv q A hyp htrans).trans
    (MulEquiv.arrowCongr (chainEquiv q).symm (MulEquiv.refl (Multiplicative ℤ)))

include htrans in
/-- A line bundle on the exceptional locus of exponent zero on every curve is trivial. -/
theorem chain_trivial_of_degree_zero (L : InvertibleSheaf (chainScheme q A))
    (hL : ∀ idx : FinalIndex.{u} q, componentExponent k (chainScheme q A)
      {lineComponent (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
        (chainCurve_distinct q A hyp) idx}
      (lineIdentification (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
        (chainCurve_distinct q A hyp)
        (lineComponent (chainScheme q A) (chainCurve q A) (chainCurve_cover q A)
          (chainCurve_distinct q A hyp) idx)) L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit (chainScheme q A).ringCatSheaf) :=
  trivial_of_degree_zero_of_configuration (chainScheme q A) (chainInclusion q A)
    (A.stage (q + 1)).structureMap (chain_transversalConfiguration q A hyp htrans) (chain_dim q A)
    (chain_isTree q A hyp) (chainCurve q A) (chainCurve_cover q A) (chainCurve_distinct q A hyp)
    L hL

end Picard

/-- Universe check: the statement at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (A₀ : PlaneChartedScheme k₀) (q₀ : ℕ)
    [NoetherianSpace (chainStage q₀ A₀)] [IsLocallyNoetherian (chainStage q₀ A₀)]
    [LocallyOfFiniteType (A₀.stage (q₀ + 1)).structureMap]
    (hyp : ChainSinglePoints q₀ A₀) (htrans : ChainTransversal q₀ A₀ hyp) :
    (chainScheme q₀ A₀).Pic ≃* (Fin (q₀ + 1) → Multiplicative ℤ) :=
  chainPicardEquivFin q₀ A₀ hyp htrans

end KltDP.Examples.FrobeniusExceptionalChainPicard
