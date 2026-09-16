import KltDP.Examples.FrobeniusTowerTransportPicardRelation
import KltDP.Examples.FrobeniusMultiCentreGraphNewest

/-!
# The class table on the cluster opens of `S_{p,n}`

The surface `S_{p,n} = multiSurface (q+1) n a` (`p = q + 1`) maps to the top stage
`selectedStage (q+1) (a i) (q+1)` of the translated contact tower over each centre `(a i, (a i)^p)`;
over the open `isoOpen q n a i` of the tower (the complement of the other centres) this map is an
isomorphism from the cluster open `isoPreimage q n a i` of `S_{p,n}` (accepted
`FrobeniusMultiCentreGraphNewest`: `isoMap q n a i = isoPreimage.ι ≫ towerProjection`, an open
immersion with image `isoOpen`, `towerProjection ∣_ isoOpen` being an isomorphism).

The classes of the translated tower's own curves (`FrobeniusTowerTransportClasses`,
`FrobeniusTowerTransportPicardRelation`) are restricted to the cluster open along `isoMap`
(`clusterHom`, the Picard pullback along the open immersion), and every clause of the class table
of the translated tower on its top stage — `B`, `C_j`, `F̃`, `P`, the total transforms, and the
Picard fibre relation — holds between the restricted classes (`clusterClassTable`).

Scope: the cluster classes are *defined* as restrictions of the translated tower's classes; their
identification with the classes of the curves of `S_{p,n}` itself (the kernel lines of the actual
curve inclusions into `S_{p,n}`, through the base change of the kernels along the open immersion
`isoMap`) is not treated here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusMultiCentreClassTable

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusContactTowerSelectedPoint FrobeniusTranslatedCharts FrobeniusTowerTransportClasses
  FrobeniusTowerTransportPicardRelation FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreSurface
  FrobeniusProjectivePoints

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k) (i : Fin n)

/-- The cluster open of `S_{p,n}` over the `i`-th centre. -/
abbrev clusterScheme : Scheme.{u} := (isoPreimage q n a i).toScheme

/-- Restriction of Picard classes from the top stage of the `i`-th translated tower to the cluster
open of `S_{p,n}`, along the open immersion `isoMap`. -/
abbrev clusterHom :
    Additive (selectedStage (q + 1) (a i) (q + 1)).Pic →+ Additive (clusterScheme q n a i).Pic :=
  (schemePicardPullbackHom (isoMap q n a i)).toAdditive

/-- `isoMap` is the inclusion of the cluster open followed by the projection `S_{p,n} ⟶ tower`: the
restricted class is the restriction to the cluster open of the pullback along the projection. -/
theorem clusterHom_apply (c : Additive (selectedStage (q + 1) (a i) (q + 1)).Pic) :
    clusterHom q n a i c =
      (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        ((schemePicardPullbackHom (towerProjection (q + 1) n a i)).toAdditive c) := by
  change (schemePicardPullbackHom (isoMap q n a i)).toAdditive c = _
  rw [isoMap_eq, picardPullback_toAdditive_comp]

/-! ## The cluster classes -/

/-- `B` (residual exponent `m`) on the cluster open. -/
def clusterStrictCurveClass (m : ℕ) : Additive (clusterScheme q n a i).Pic :=
  clusterHom q n a i (translatedStrictCurveClass (q + 1) (a i) (q + 1) m)

/-- `C_j` on the cluster open. -/
def clusterOldExceptionalStrictClass (j : ℕ) (h : j + 1 + 1 ≤ q + 1) :
    Additive (clusterScheme q n a i).Pic :=
  clusterHom q n a i (translatedOldExceptionalStrictClass (q + 1) (a i) (q + 1) j h)

/-- `F̃` on the cluster open. -/
def clusterFiberClass : Additive (clusterScheme q n a i).Pic :=
  clusterHom q n a i (translatedFiberClass (q + 1) (a i) (q + 1))

/-- `P` (the newest exceptional curve `E_q`) on the cluster open. -/
def clusterStepExceptionalClass : Additive (clusterScheme q n a i).Pic :=
  clusterHom q n a i (translatedStepExceptionalClass (q + 1) (a i) q)

/-- The total transform `E_j^{(q+1)}` on the cluster open. -/
def clusterTotalExceptionalClass (j : Fin (q + 1)) : Additive (clusterScheme q n a i).Pic :=
  clusterHom q n a i (translatedTotalExceptionalClass (q + 1) (a i) (q + 1) j)

/-- The total transform `a` on the cluster open. -/
def clusterFirstFiberTotalClass : Additive (clusterScheme q n a i).Pic :=
  clusterHom q n a i (translatedFirstFiberTotalClass (q + 1) (a i) (q + 1))

/-- The total transform `b` on the cluster open. -/
def clusterSecondFiberTotalClass : Additive (clusterScheme q n a i).Pic :=
  clusterHom q n a i (translatedSecondFiberTotalClass (q + 1) (a i) (q + 1))

/-- The total transform `F_0^{(q+1)}` of the stage-`0` fibre on the cluster open. -/
def clusterFiberZeroTotalClass : Additive (clusterScheme q n a i).Pic :=
  clusterHom q n a i (translatedFiberZeroTotalClass (q + 1) (a i) (q + 1))

/-- The total transform `π^* b` of the class of the fibre `y = 1 + a^p` on the cluster open. -/
def clusterFiberPullbackClass : Additive (clusterScheme q n a i).Pic :=
  clusterHom q n a i
    ((schemePicardPullbackHom
      (between (translatedInitial (q + 1) (a i)) (Nat.zero_le (q + 1)))).toAdditive
        (translatedSecondFiberClass (q + 1) (a i)))

/-! ## The class table on the cluster open -/

theorem clusterStrictCurveClass_tower (m : ℕ) :
    clusterStrictCurveClass q n a i m =
      (m + (q + 1)) • clusterFirstFiberTotalClass q n a i + clusterSecondFiberTotalClass q n a i -
        ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j := by
  unfold clusterStrictCurveClass clusterFirstFiberTotalClass clusterSecondFiberTotalClass
    clusterTotalExceptionalClass
  rw [translatedStrictCurveClass_tower, map_sub, map_add, map_nsmul, map_sum]

/-- The graph relation `B = (q+1)·a + b − Σ E_j` (residual exponent `0`) on the cluster open. -/
theorem clusterStrictCurveClass_zero :
    clusterStrictCurveClass q n a i 0 =
      (q + 1) • clusterFirstFiberTotalClass q n a i + clusterSecondFiberTotalClass q n a i -
        ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j := by
  rw [clusterStrictCurveClass_tower, zero_add]

theorem clusterOldExceptionalStrictClass_eq (j : ℕ) (h : j + 1 + 1 ≤ q + 1) :
    clusterOldExceptionalStrictClass q n a i j h =
      clusterTotalExceptionalClass q n a i ⟨j, by omega⟩ -
        clusterTotalExceptionalClass q n a i ⟨j + 1, by omega⟩ := by
  unfold clusterOldExceptionalStrictClass clusterTotalExceptionalClass
  rw [translatedOldExceptionalStrictClasses_tower, map_sub]

theorem clusterFiberClass_tower :
    clusterFiberClass q n a i =
      clusterFiberZeroTotalClass q n a i -
        ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j := by
  unfold clusterFiberClass clusterFiberZeroTotalClass clusterTotalExceptionalClass
  rw [translatedFiberClass_tower, map_sub, map_sum]

theorem clusterTotalExceptionalClass_last :
    clusterTotalExceptionalClass q n a i (Fin.last q) = clusterStepExceptionalClass q n a i := by
  unfold clusterTotalExceptionalClass clusterStepExceptionalClass
  rw [translatedTotalExceptionalClass_last]

/-- **The Picard fibre relation on the cluster open**:
`π^* b = F̃ + Σ_{j<q} (j+1)·C_j + (q+1)·P`. -/
theorem cluster_fiber_picard_relation :
    clusterFiberPullbackClass q n a i =
      clusterFiberClass q n a i +
        ∑ j : Fin q, (j.val + 1) • clusterOldExceptionalStrictClass q n a i j.val (by omega) +
        (q + 1) • clusterTotalExceptionalClass q n a i (Fin.last q) := by
  unfold clusterFiberPullbackClass clusterFiberClass clusterOldExceptionalStrictClass
    clusterTotalExceptionalClass
  rw [translated_fiber_picard_relation, map_add, map_add, map_sum, map_nsmul]
  simp_rw [map_nsmul]

/-- **The class table on the cluster open of `S_{p,n}` over the `i`-th centre**: the relations of
the translated tower's top stage between the restricted classes. -/
theorem clusterClassTable :
    (∀ m : ℕ, clusterStrictCurveClass q n a i m =
      (m + (q + 1)) • clusterFirstFiberTotalClass q n a i + clusterSecondFiberTotalClass q n a i -
        ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j) ∧
    (clusterStrictCurveClass q n a i 0 =
      (q + 1) • clusterFirstFiberTotalClass q n a i + clusterSecondFiberTotalClass q n a i -
        ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j) ∧
    (∀ (j : ℕ) (h : j + 1 + 1 ≤ q + 1), clusterOldExceptionalStrictClass q n a i j h =
      clusterTotalExceptionalClass q n a i ⟨j, by omega⟩ -
        clusterTotalExceptionalClass q n a i ⟨j + 1, by omega⟩) ∧
    (clusterFiberClass q n a i =
      clusterFiberZeroTotalClass q n a i -
        ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j) ∧
    (clusterTotalExceptionalClass q n a i (Fin.last q) = clusterStepExceptionalClass q n a i) ∧
    (clusterFiberPullbackClass q n a i =
      clusterFiberClass q n a i +
        ∑ j : Fin q, (j.val + 1) • clusterOldExceptionalStrictClass q n a i j.val (by omega) +
        (q + 1) • clusterTotalExceptionalClass q n a i (Fin.last q)) :=
  ⟨clusterStrictCurveClass_tower q n a i, clusterStrictCurveClass_zero q n a i,
    clusterOldExceptionalStrictClass_eq q n a i, clusterFiberClass_tower q n a i,
    clusterTotalExceptionalClass_last q n a i, cluster_fiber_picard_relation q n a i⟩

end KltDP.Examples.FrobeniusMultiCentreClassTable
