import KltDP.Examples.FrobeniusMultiCentreCanonicalOpenComparison
import KltDP.Examples.FrobeniusMultiCentreCrossClusterRestrictions

/-!
# The actual canonical formula on every original finite-centre covering open

The original cluster comparison restricts the proved iterated tower formula.
The existing total exceptional classes from other clusters vanish there; all
exceptional classes vanish on the original complement of the centres. Thus
the actual canonical class and the proposed global expression have the same
restrictions on the original cover. This is a local conclusion only: no
injectivity of Picard restriction or global line isomorphism is inferred.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalLocalFormula

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
open FrobeniusContactTowerSelectedPoint FrobeniusTowerTransportClasses
open FrobeniusContactTowerCanonicalIteration FrobeniusMultiCentreSurface
open FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreClassTable
open FrobeniusMultiCentreCurveKernels FrobeniusMultiCentreIsoOpenClasses
open FrobeniusMultiCentreCrossClusterRestrictions FrobeniusMultiCentreCanonicalOpenComparison

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The iterated original tower formula, restricted through the actual global canonical comparison. -/
theorem clusterCanonicalClass_formula (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) :
    (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        (multiCanonicalClass (q + 1) n a ha) =
      (schemePicardPullbackHom
        ((isoPreimage q n a i).ι ≫ multiProjection (q + 1) n a)).toAdditive
        (originalCanonicalClass (k := k) 0) +
          ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j := by
  rw [clusterCanonicalClass_eq, translatedCanonicalClass_tower, map_add, map_sum,
    ← picardPullback_toAdditive_comp, ← ι_multiProjection]
  rfl

/-- On a cluster open, the total exceptional sum retains exactly its own original cluster. -/
theorem totalExceptionalSum_restrict_cluster (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (∑ i' : Fin n, ∑ j : Fin (q + 1),
      (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        (exceptionalClass (q + 1) n a i' j)) =
      ∑ j : Fin (q + 1), clusterTotalExceptionalClass q n a i j := by
  classical
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro j _
    exact exceptionalClass_restrict q n a i j
  · intro i' _ hne
    exact Finset.sum_eq_zero fun j _ => exceptionalClass_restrict_cluster q n a hne j
  · intro h
    exact False.elim (h (Finset.mem_univ i))

/-- The actual canonical class and the full original exceptional expression agree on each cluster. -/
theorem canonicalFormula_restrict_cluster (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) :
    (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        (multiCanonicalClass (q + 1) n a ha) =
      (schemePicardPullbackHom (isoPreimage q n a i).ι).toAdditive
        ((schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
          (originalCanonicalClass (k := k) 0) +
            ∑ i' : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i' j) := by
  rw [map_add]
  simp only [map_sum]
  rw [← picardPullback_toAdditive_comp, totalExceptionalSum_restrict_cluster]
  exact clusterCanonicalClass_formula q n a ha i

/-- On the original complement the same formula follows from the actual blowdown open map. -/
theorem canonicalFormula_restrict_complement (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) :
    (schemePicardPullbackHom (blowdownIsoOpen q n a).ι).toAdditive
        (multiCanonicalClass (q + 1) n a ha) =
      (schemePicardPullbackHom (blowdownIsoOpen q n a).ι).toAdditive
        ((schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
          (originalCanonicalClass (k := k) 0) +
            ∑ i : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j) := by
  rw [complementCanonicalClass_eq, map_add]
  simp only [map_sum, exceptionalClass_restrict_isoOpen, Finset.sum_const_zero, add_zero]
  rw [← picardPullback_toAdditive_comp, ← blowdownMap_eq]

/-- This is the already proved original cover, indexed by the complement and actual clusters. -/
def canonicalCoverOpen (q n : ℕ) (a : Fin n → k) :
    Option (Fin n) → (multiSurface (q + 1) n a).Opens
  | none => blowdownIsoOpen q n a
  | some i => isoPreimage q n a i

theorem mem_canonicalCoverOpen (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (x : multiSurface (q + 1) n a) :
    ∃ c, x ∈ canonicalCoverOpen q n a c := by
  rcases cluster_cover q n a ha x with h | ⟨i, hi⟩
  · exact ⟨none, h⟩
  · exact ⟨some i, hi⟩

/-- The actual canonical formula on every member of the original finite-centre cover.
This does not assert equality of the global Picard classes. -/
theorem canonicalFormula_restrict_cover (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (c : Option (Fin n)) :
    (schemePicardPullbackHom (canonicalCoverOpen q n a c).ι).toAdditive
        (multiCanonicalClass (q + 1) n a ha) =
      (schemePicardPullbackHom (canonicalCoverOpen q n a c).ι).toAdditive
        ((schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
          (originalCanonicalClass (k := k) 0) +
            ∑ i : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j) := by
  cases c with
  | none => exact canonicalFormula_restrict_complement q n a ha
  | some i => exact canonicalFormula_restrict_cluster q n a ha i

end KltDP.Examples.FrobeniusMultiCentreCanonicalLocalFormula
