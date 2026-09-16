import KltDP.Geometry.RationalTreePicardChainOfCurves
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian
import KltDP.Examples.FrobeniusMultiCentreExceptional

/-!
# The exceptional chains of the multi-centre surface `S_{p,n}` and their Picard groups

BRIEF22, task 1. Write `p = q + 1`. Lane F realises the exceptional curves of `S_{p,n} =
multiSurface (q+1) n a` as closed immersions `exceptionalCurveι q n a i idx` (`i : Fin n` the
tower, `idx : FinalIndex q` the curve `C_{i,j+1}` or the newest fibre `P_i`), each isomorphic to
the accepted final component of the `i`-th tower (`exceptionalCurveIso`), hence to `P¹`
(`curveIso`: lane F's `previousStrictIsoProjectiveLine` for the older curves, the accepted
`previousFiberIso` for `P_i`). This module:

* proves that `S_{p,n}` is locally Noetherian and a Noetherian space
  (`multiSurface_isLocallyNoetherian`, `multiSurface_noetherianSpace`: it is proper, hence of
  finite type and quasi-compact, over the field `k`; `LocallyOfFiniteTypeNoetherian`);
* enumerates the `i`-th exceptional chain `C_{i1} ∪ ⋯ ∪ C_{iq} ∪ P_i` by `Fin (q + 1)`
  (`chainCurve i j`, task 19's `chainMember`), transports the accepted incidences of lane F
  (adjacent curves meet, non-adjacent curves are disjoint: `support_nonempty`,
  `support_disjoint`) and builds the chain data `CurveChain.ChainData` of
  `RationalTreePicardChainOfCurves` for each tower, modulo lane F's single-point hypothesis
  `SinglePoints` (adjacent curves of one tower meet in at most one point);
* obtains the `i`-th chain `towerChain i` as a reduced closed subscheme of `S_{p,n}` and, for `k`
  algebraically closed and modulo the transversality hypothesis `TowerTransversal` (BRIEF18's
  stalk form at the chain points), **`Pic(towerChain i) ≃* ℤ^{q+1}`** (`towerChainPicardEquiv`),
  the bijectivity of the multidegree map and the degree-zero clause — the extension of task 20's
  `chainPicardEquivFin_of_tower` from the tower `T_i` to `S_{p,n}`;
* defines the whole exceptional locus `exceptionalScheme` (reduced closed subscheme on the union
  of all `n(q+1)` curves), the closed immersions `towerToLocus i` of the chains into it, the
  restriction homomorphisms `restrictToTower i : Pic(locus) →* Pic(towerChain i)` and the
  tower-by-tower degree `exceptionalDegree : Pic(locus) →* ℤ^{n(q+1)}`; the curves of different
  towers are disjoint (lane F's `exceptionalSupport_disjoint_of_ne`), so the locus is the disjoint
  union of the `n` chains.

**Not proved here** (recorded in `LEMMA22_PROGRESS.md`, Task 22): that `exceptionalDegree` is
bijective, i.e. `Pic(locus) ≃* ℤ^{n(q+1)}`. The accepted Lemma 2.2 (`rationalTreePicard_of_configuration`)
and both of its halves require the incidence graph to be a *tree* (connected), and neither the
accepted tree nor the pinned Mathlib has the Picard group of a disjoint union of schemes (a clopen
decomposition `Z = Z_1 ⊔ ⋯ ⊔ Z_n` gives `Pic Z ≃ ∏ Pic Z_i`), which is exactly the missing step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreChainPicard

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusPreviousStrictIsoProjectiveLine FrobeniusGlobalExceptionalSuccessor
  FrobeniusTranslatedCharts FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
  FrobeniusExceptionalChainPicard

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-! ## `S_{p,n}` is Noetherian -/

instance multiSurface_isLocallyNoetherian : IsLocallyNoetherian (multiSurface (q + 1) n a) :=
  haveI : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  isLocallyNoetherian_of_locallyOfFiniteType_spec (multiStructure (q + 1) n a)

instance multiSurface_noetherianSpace : NoetherianSpace (multiSurface (q + 1) n a) :=
  haveI : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec (multiStructure (q + 1) n a)

section Tower

variable [IsAlgClosed k] (ha : Function.Injective a)

/-! ## The curves of the `i`-th chain -/

/-- Each final exceptional component of the `i`-th tower is a projective line (lane F's
`previousStrictIsoProjectiveLine` for the older curves, the accepted `previousFiberIso` for the
newest fibre). -/
def componentIso (i : Fin n) : (idx : FinalIndex.{0} q) →
    (finalComponent (translatedInitial (q + 1) (a i)) q idx ≅ projectiveSpace k 1)
  | Sum.inl j => previousStrictIsoProjectiveLine ((translatedInitial (q + 1) (a i)).stage j.val)
  | Sum.inr _ => previousFiberIso ((translatedInitial (q + 1) (a i)).stage q)

/-- `E_{i,idx} ≅ P¹`. -/
def curveIso (i : Fin n) (idx : FinalIndex.{0} q) :
    exceptionalCurve q n a i idx ≅ projectiveSpace k 1 :=
  exceptionalCurveIso q n a ha i idx ≪≫ componentIso q n a i idx

/-- The `j`-th curve of the `i`-th exceptional chain (`C_{i,j+1}` for `j < q`, `P_i` for
`j = q`), as a closed immersion of `P¹` into `S_{p,n}`. -/
def chainCurve (i : Fin n) (j : Fin (q + 1)) : projectiveSpace k 1 ⟶ multiSurface (q + 1) n a :=
  (curveIso q n a ha i (chainMember.{0} q j)).inv ≫ exceptionalCurveι q n a i (chainMember.{0} q j)

instance chainCurve_isClosedImmersion (i : Fin n) (j : Fin (q + 1)) :
    IsClosedImmersion (chainCurve q n a ha i j) := by
  unfold chainCurve
  infer_instance

theorem range_chainCurve (i : Fin n) (j : Fin (q + 1)) :
    Set.range (chainCurve q n a ha i j).base =
      exceptionalSupport q n a i (chainMember.{0} q j) := by
  unfold exceptionalSupport
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(curveIso q n a ha i (chainMember.{0} q j)).inv.base p,
      (Scheme.comp_base_apply _ _ p).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨(curveIso q n a ha i (chainMember.{0} q j)).hom.base z, ?_⟩
    have h : (curveIso q n a ha i (chainMember.{0} q j)).inv.base
        ((curveIso q n a ha i (chainMember.{0} q j)).hom.base z) = z := by
      rw [← Scheme.comp_base_apply, Iso.hom_inv_id]
      rfl
    show (exceptionalCurveι q n a i (chainMember.{0} q j)).base
      ((curveIso q n a ha i (chainMember.{0} q j)).inv.base
        ((curveIso q n a ha i (chainMember.{0} q j)).hom.base z)) = _
    rw [h]

/-! ## The incidences of one chain -/

include ha in
theorem support_nonempty_last (m : ℕ) (hq : q = m + 1) (i : Fin n) :
    (exceptionalSupport q n a i (Sum.inl ⟨m, by omega⟩ : FinalIndex.{0} q) ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit : FinalIndex.{0} q)).Nonempty := by
  subst hq
  exact exceptionalSupport_last_adjacent m n a ha i

include ha in
/-- Adjacent curves of one chain meet (lane F). -/
theorem support_nonempty (i : Fin n) (j : Fin q) :
    (exceptionalSupport q n a i (chainMember.{0} q j.castSucc) ∩
      exceptionalSupport q n a i (chainMember.{0} q j.succ)).Nonempty := by
  rw [chainMember_of_lt q j.castSucc (by rw [Fin.coe_castSucc]; exact j.isLt)]
  by_cases h : j.val + 1 < q
  · rw [chainMember_of_lt q j.succ (by rw [Fin.val_succ]; exact h)]
    exact exceptionalSupport_adjacent q n a ha i j.val h
  · rw [chainMember_of_not_lt q j.succ (by rw [Fin.val_succ]; exact h)]
    exact support_nonempty_last q n a ha j.val (by have := j.isLt; omega) i

omit [IsAlgClosed k] in
/-- Non-adjacent curves of one chain are disjoint (lane F). -/
theorem support_disjoint (i : Fin n) (j j' : Fin (q + 1)) (hjj' : j.val + 1 < j'.val) :
    Disjoint (exceptionalSupport q n a i (chainMember.{0} q j))
      (exceptionalSupport q n a i (chainMember.{0} q j')) := by
  have hj' := j'.isLt
  rw [chainMember_of_lt q j (by omega)]
  by_cases h : j'.val < q
  · rw [chainMember_of_lt q j' h]
    exact exceptionalSupport_disjoint_nonadjacent q n a i ⟨j.val, by omega⟩ ⟨j'.val, h⟩ hjj'
  · rw [chainMember_of_not_lt q j' h]
    exact exceptionalSupport_disjoint_newest q n a i ⟨j.val, by omega⟩
      (show j.val + 1 < q by omega)

/-- **Hypothesis awaited from lane F**: adjacent exceptional curves of one tower of `S_{p,n}` meet
in at most one point (with `support_nonempty`: in exactly one point). -/
structure SinglePoints : Prop where
  old : ∀ (i : Fin n) (j : ℕ) (hj : j + 1 < q),
    (exceptionalSupport q n a i (Sum.inl ⟨j, by omega⟩ : FinalIndex.{0} q) ∩
      exceptionalSupport q n a i (Sum.inl ⟨j + 1, hj⟩ : FinalIndex.{0} q)).Subsingleton
  newest : ∀ (i : Fin n) (m : ℕ) (hq : q = m + 1),
    (exceptionalSupport q n a i (Sum.inl ⟨m, by omega⟩ : FinalIndex.{0} q) ∩
      exceptionalSupport q n a i (Sum.inr PUnit.unit : FinalIndex.{0} q)).Subsingleton

omit [IsAlgClosed k] in
theorem support_subsingleton (hyp : SinglePoints q n a) (i : Fin n) (j : Fin q) :
    (exceptionalSupport q n a i (chainMember.{0} q j.castSucc) ∩
      exceptionalSupport q n a i (chainMember.{0} q j.succ)).Subsingleton := by
  rw [chainMember_of_lt q j.castSucc (by rw [Fin.coe_castSucc]; exact j.isLt)]
  by_cases h : j.val + 1 < q
  · rw [chainMember_of_lt q j.succ (by rw [Fin.val_succ]; exact h)]
    exact hyp.old i j.val h
  · rw [chainMember_of_not_lt q j.succ (by rw [Fin.val_succ]; exact h)]
    exact hyp.newest i j.val (by have := j.isLt; omega)

/-- The chain data of the `i`-th exceptional chain. -/
theorem chainData (hyp : SinglePoints q n a) (i : Fin n) :
    CurveChain.ChainData (multiSurface (q + 1) n a) q (chainCurve q n a ha i) where
  subsingleton j := by
    show (Set.range (chainCurve q n a ha i j.castSucc).base ∩
      Set.range (chainCurve q n a ha i j.succ).base).Subsingleton
    rw [range_chainCurve, range_chainCurve]
    exact support_subsingleton q n a hyp i j
  nonempty j := by
    show (Set.range (chainCurve q n a ha i j.castSucc).base ∩
      Set.range (chainCurve q n a ha i j.succ).base).Nonempty
    rw [range_chainCurve, range_chainCurve]
    exact support_nonempty q n a ha i j
  disjoint j j' h := by
    show Disjoint (Set.range (chainCurve q n a ha i j).base)
      (Set.range (chainCurve q n a ha i j').base)
    rw [range_chainCurve, range_chainCurve]
    exact support_disjoint q n a i j j' h

/-! ## The `i`-th chain as a closed subscheme of `S_{p,n}` and its Picard group -/

/-- The `i`-th exceptional chain `C_{i1} ∪ ⋯ ∪ C_{iq} ∪ P_i` of `S_{p,n}`, as a reduced closed
subscheme. -/
abbrev towerChain (i : Fin n) : Scheme.{u} :=
  CurveChain.scheme (multiSurface (q + 1) n a) q (chainCurve q n a ha i)

/-- Its inclusion into `S_{p,n}`. -/
abbrev towerChainInclusion (i : Fin n) : towerChain q n a ha i ⟶ multiSurface (q + 1) n a :=
  CurveChain.inclusion (multiSurface (q + 1) n a) q (chainCurve q n a ha i)

/-- **Hypothesis awaited from lane F**: the crossings of adjacent curves in each chain are
transversal (BRIEF18's stalk form, relative to `S_{p,n}`). -/
def TowerTransversal (hyp : SinglePoints q n a) : Prop :=
  ∀ i : Fin n, CurveChain.Transversal (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
    (chainData q n a ha hyp i)

variable (hyp : SinglePoints q n a) (htrans : TowerTransversal q n a ha hyp)

include htrans in
/-- **The multidegree map of the `i`-th exceptional chain of `S_{p,n}` is bijective** (modulo lane
F's single points and transversality). -/
theorem towerChain_rationalTreePicard (i : Fin n) :
    Function.Bijective (multidegreeHom k (towerChain q n a ha i)
      (lineIdentification (towerChain q n a ha i)
        (CurveChain.curve (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
        (CurveChain.curve_cover (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
        (CurveChain.curve_distinct (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
          (chainData q n a ha hyp i)))) :=
  CurveChain.rationalTreePicard (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
    (multiStructure (q + 1) n a) (chainData q n a ha hyp i) (htrans i)

/-- **`Pic(C_{i1} ∪ ⋯ ∪ C_{iq} ∪ P_i) ≃* ℤ^{q+1}` on `S_{p,n}`.** -/
def towerChainPicardEquiv (i : Fin n) :
    (towerChain q n a ha i).Pic ≃* (Fin (q + 1) → Multiplicative ℤ) :=
  CurveChain.picardEquiv (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
    (multiStructure (q + 1) n a) (chainData q n a ha hyp i) (htrans i)

include htrans in
/-- A line bundle on the `i`-th chain with exponent zero on every curve is trivial. -/
theorem towerChain_trivial_of_degree_zero (i : Fin n) (L : InvertibleSheaf (towerChain q n a ha i))
    (hL : ∀ idx : ULift.{u} (Fin (q + 1)), componentExponent k (towerChain q n a ha i)
      {lineComponent (towerChain q n a ha i)
        (CurveChain.curve (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
        (CurveChain.curve_cover (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
        (CurveChain.curve_distinct (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
          (chainData q n a ha hyp i)) idx}
      (lineIdentification (towerChain q n a ha i)
        (CurveChain.curve (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
        (CurveChain.curve_cover (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
        (CurveChain.curve_distinct (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
          (chainData q n a ha hyp i))
        (lineComponent (towerChain q n a ha i)
          (CurveChain.curve (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
          (CurveChain.curve_cover (multiSurface (q + 1) n a) q (chainCurve q n a ha i))
          (CurveChain.curve_distinct (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
            (chainData q n a ha hyp i)) idx)) L = 0) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit (towerChain q n a ha i).ringCatSheaf) :=
  CurveChain.trivial_of_degree_zero (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
    (multiStructure (q + 1) n a) (chainData q n a ha hyp i) (htrans i) L hL

/-! ## The whole exceptional locus: a disjoint union of the `n` chains -/

/-- The support of the whole exceptional locus of `S_{p,n}`. -/
def exceptionalLocus : Set (multiSurface (q + 1) n a) :=
  ⋃ i : Fin n, ⋃ idx : FinalIndex.{0} q, exceptionalSupport q n a i idx

omit [IsAlgClosed k] in
theorem exceptionalLocus_isClosed : IsClosed (exceptionalLocus q n a) :=
  isClosed_iUnion_of_finite fun i =>
    isClosed_iUnion_of_finite fun idx => exceptionalSupport_isClosed q n a i idx

/-- Its vanishing ideal sheaf. -/
def exceptionalIdeal : (multiSurface (q + 1) n a).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨exceptionalLocus q n a, exceptionalLocus_isClosed q n a⟩

/-- The exceptional locus as a reduced closed subscheme of `S_{p,n}`. -/
def exceptionalScheme : Scheme.{u} := (exceptionalIdeal q n a).glueData.glued

/-- Its inclusion into `S_{p,n}`. -/
def exceptionalInclusion : exceptionalScheme q n a ⟶ multiSurface (q + 1) n a :=
  (exceptionalIdeal q n a).gluedTo

instance exceptionalInclusion_isClosedImmersion : IsClosedImmersion (exceptionalInclusion q n a) :=
  (exceptionalIdeal q n a).gluedTo_isClosedImmersion

instance exceptionalScheme_isReduced : AlgebraicGeometry.IsReduced (exceptionalScheme q n a) :=
  (exceptionalIdeal q n a).glued_isReduced
    (Scheme.IdealSheafData.vanishingIdeal_support (I := exceptionalIdeal q n a)).symm

omit [IsAlgClosed k] in
theorem range_exceptionalInclusion :
    Set.range (exceptionalInclusion q n a).base = exceptionalLocus q n a :=
  (exceptionalIdeal q n a).range_gluedTo

/-- The `i`-th chain lies in the exceptional locus. -/
theorem towerChain_range_subset (i : Fin n) :
    Set.range (towerChainInclusion q n a ha i).base ⊆ exceptionalLocus q n a := by
  rw [show Set.range (towerChainInclusion q n a ha i).base =
    CurveChain.locus (multiSurface (q + 1) n a) q (chainCurve q n a ha i) from
    CurveChain.range_inclusion _ q _]
  intro x hx
  unfold CurveChain.locus at hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  rw [show CurveChain.support (multiSurface (q + 1) n a) q (chainCurve q n a ha i) j =
    exceptionalSupport q n a i (chainMember.{0} q j) from range_chainCurve q n a ha i j] at hj
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨chainMember.{0} q j, hj⟩⟩

theorem exceptionalIdeal_le_ker (i : Fin n) :
    exceptionalIdeal q n a ≤ (towerChainInclusion q n a ha i).ker := by
  refine le_trans ?_ (vanishingIdeal_le_ker (towerChainInclusion q n a ha i)
    ⟨Set.range (towerChainInclusion q n a ha i).base,
      (towerChainInclusion q n a ha i).isClosedEmbedding.isClosed_range⟩ rfl)
  exact Scheme.IdealSheafData.vanishingIdeal_antimono (towerChain_range_subset q n a ha i)

/-- The `i`-th chain as a closed subscheme of the exceptional locus. -/
def towerToLocus (i : Fin n) : towerChain q n a ha i ⟶ exceptionalScheme q n a :=
  liftGluedTo (exceptionalIdeal q n a) (towerChainInclusion q n a ha i)
    (exceptionalIdeal_le_ker q n a ha i)

theorem towerToLocus_comp (i : Fin n) :
    towerToLocus q n a ha i ≫ exceptionalInclusion q n a = towerChainInclusion q n a ha i :=
  liftGluedTo_gluedTo _ _ _

instance towerToLocus_isClosedImmersion (i : Fin n) : IsClosedImmersion (towerToLocus q n a ha i) := by
  haveI : IsClosedImmersion (towerToLocus q n a ha i ≫ exceptionalInclusion q n a) := by
    rw [towerToLocus_comp]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (exceptionalInclusion q n a)

/-- Curves of different towers are disjoint (lane F): the exceptional locus is the disjoint union
of the `n` chains. -/
theorem towerChain_range_disjoint {i i' : Fin n} (hii' : i ≠ i') :
    Disjoint (Set.range (towerChainInclusion q n a ha i).base)
      (Set.range (towerChainInclusion q n a ha i').base) := by
  rw [show Set.range (towerChainInclusion q n a ha i).base =
    CurveChain.locus (multiSurface (q + 1) n a) q (chainCurve q n a ha i) from
    CurveChain.range_inclusion _ q _,
    show Set.range (towerChainInclusion q n a ha i').base =
    CurveChain.locus (multiSurface (q + 1) n a) q (chainCurve q n a ha i') from
    CurveChain.range_inclusion _ q _]
  unfold CurveChain.locus
  refine Set.disjoint_iUnion_left.mpr fun j => Set.disjoint_iUnion_right.mpr fun j' => ?_
  rw [show CurveChain.support (multiSurface (q + 1) n a) q (chainCurve q n a ha i) j =
    exceptionalSupport q n a i (chainMember.{0} q j) from range_chainCurve q n a ha i j,
    show CurveChain.support (multiSurface (q + 1) n a) q (chainCurve q n a ha i') j' =
    exceptionalSupport q n a i' (chainMember.{0} q j') from range_chainCurve q n a ha i' j']
  exact exceptionalSupport_disjoint_of_ne q n a ha hii' _ _

/-- Restriction of Picard classes from the exceptional locus to the `i`-th chain. -/
def restrictToTower (i : Fin n) : (exceptionalScheme q n a).Pic →* (towerChain q n a ha i).Pic :=
  schemePicardPullbackHom (towerToLocus q n a ha i)

/-- Restricting from `S_{p,n}` to the locus and then to the `i`-th chain is restricting to the
chain. -/
theorem restrictToTower_comp (i : Fin n) :
    (restrictToTower q n a ha i).comp (schemePicardPullbackHom (exceptionalInclusion q n a)) =
      schemePicardPullbackHom (towerChainInclusion q n a ha i) := by
  rw [← towerToLocus_comp q n a ha i, schemePicardPullbackHom_comp]
  rfl

/-- **The tower-by-tower degree of the exceptional locus** `Pic(locus) →* ℤ^{n(q+1)}`: restrict to
each chain and take its multidegree. Its bijectivity (the Picard group of the disjoint union of
the `n` chains) is NOT proved here; see the module docstring. -/
def exceptionalDegree :
    (exceptionalScheme q n a).Pic →* (Fin n × Fin (q + 1) → Multiplicative ℤ) :=
  Pi.monoidHom fun p => (Pi.evalMonoidHom (fun _ : Fin (q + 1) => Multiplicative ℤ) p.2).comp
    ((towerChainPicardEquiv q n a ha hyp htrans p.1).toMonoidHom.comp (restrictToTower q n a ha p.1))

end Tower

/-- Universe check at universe `0`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (q₀ n₀ : ℕ) (a₀ : Fin n₀ → k₀)
    (ha₀ : Function.Injective a₀) (hyp : SinglePoints q₀ n₀ a₀)
    (htrans : TowerTransversal q₀ n₀ a₀ ha₀ hyp) (i : Fin n₀) :
    (towerChain q₀ n₀ a₀ ha₀ i).Pic ≃* (Fin (q₀ + 1) → Multiplicative ℤ) :=
  towerChainPicardEquiv q₀ n₀ a₀ ha₀ hyp htrans i

end KltDP.Examples.FrobeniusMultiCentreChainPicard
