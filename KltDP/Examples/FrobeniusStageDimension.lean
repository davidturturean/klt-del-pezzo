import KltDP.Examples.FrobeniusTowerFunctionField
import KltDP.Examples.FrobeniusStrictTransformStepPuncture
import KltDP.Examples.FrobeniusGraphPicardClassCharts
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Geometry.ProperOpenDimension
import KltDP.Compatibility.PolynomialDimension
import KltDP.Topology.DimensionOpenCover

/-!
# Krull dimension two of the contact-tower stages

`topologicalKrullDim (projectiveContactStage n) = 2` for every `n`, over an algebraically closed
field `k`.

* The polynomial plane `k[u][v]` is the two-variable polynomial ring (`planeRingMvPolynomialEquiv`),
  so `Spec k[u][v]` has dimension two by the accepted `polynomial_ringKrullDim`
  (`plane_topologicalKrullDim`).
* The projective product is covered by the four accepted polynomial charts, each an open piece
  homeomorphic to the plane, so it has dimension two (`projectiveProduct_topologicalKrullDim`;
  accepted open-cover bound and open-embedding lower bound). No algebraic closedness is used here.
* Each step projection `stage (n+1) → stage n` is proper (accepted) and an isomorphism over the
  nonempty puncture of the centre (accepted `stepProjection_puncture_isIso`,
  `initialPuncture_nonempty`), both stages are integral (accepted `stage_isIntegral`), and the
  structure morphisms are of finite type (they are proper); the accepted
  `topologicalKrullDim_eq_of_proper_isomorphism_open` (which needs `IsAlgClosed k` for the pinned
  finite-type closed-point dimension theorem) transports the dimension up the tower
  (`projectiveContactStage_topologicalKrullDim`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStageDimension

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusProjectivePoints FrobeniusGlobalBlowupStages
open FrobeniusGraphPicardClassCharts FrobeniusStageComplement FrobeniusStrictTransformStepPuncture
open FrobeniusTowerFunctionField.PlaneChartedScheme

variable {k : Type u} [Field k]

/-- The polynomial plane `k[u][v]` is the two-variable polynomial ring. -/
def planeRingMvPolynomialEquiv : MvPolynomial (Fin 2) k ≃+* planeRing k :=
  (MvPolynomial.finSuccEquiv k 1).toRingEquiv.trans
    (Polynomial.mapEquiv ((MvPolynomial.finSuccEquiv k 0).toRingEquiv.trans
      (Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)))))

/-- `k[u][v]` has Krull dimension two. -/
theorem planeRing_ringKrullDim : ringKrullDim (planeRing k) = 2 :=
  (ringKrullDim_eq_of_ringEquiv (planeRingMvPolynomialEquiv (k := k)).symm).trans
    (KltDP.Compatibility.polynomial_ringKrullDim k 2)

/-- The polynomial plane has topological Krull dimension two. -/
theorem plane_topologicalKrullDim :
    topologicalKrullDim (Spec (CommRingCat.of (planeRing k))) = 2 :=
  (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (planeRing k)).trans planeRing_ringKrullDim

/-- Each polynomial chart of the projective product is an open piece of dimension two. -/
theorem productChart_opensRange_topologicalKrullDim (i j : Fin 2) :
    topologicalKrullDim ((productChart (k := k) i j).opensRange) = 2 := by
  have h := IsHomeomorph.topologicalKrullDim_eq _
    (productChart (k := k) i j).isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph
  exact h.symm.trans plane_topologicalKrullDim

/-- **The projective product `P¹ ×_k P¹` has dimension two**, over any field. -/
theorem projectiveProduct_topologicalKrullDim : topologicalKrullDim (projectiveProduct k) = 2 := by
  apply le_antisymm
  · refine KltDP.Topology.topologicalKrullDim_le_of_open_cover
      (fun ij : Fin 2 × Fin 2 => (productChart (k := k) ij.1 ij.2).opensRange) ?_ 2 ?_
    · intro x
      obtain ⟨i, j, y, hy⟩ := productCharts_cover x
      exact ⟨(i, j), y, hy⟩
    · intro ij
      exact (productChart_opensRange_topologicalKrullDim ij.1 ij.2).le
  · calc
      (2 : WithBot ℕ∞) = topologicalKrullDim (Spec (CommRingCat.of (planeRing k))) :=
        plane_topologicalKrullDim.symm
      _ ≤ topologicalKrullDim (projectiveProduct k) :=
        KltDP.Topology.topologicalKrullDim_le_of_isOpenEmbedding _
          (productChart (k := k) 0 0).isOpenEmbedding

local instance stageDimensionInitialIsIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **Every stage of the Frobenius contact tower has dimension two** over an algebraically closed
field: the step projections are proper and isomorphisms over the nonempty puncture of the centre. -/
theorem projectiveContactStage_topologicalKrullDim [IsAlgClosed k] :
    ∀ n : ℕ, topologicalKrullDim (projectiveContactStage (k := k) n) = 2
  | 0 => projectiveProduct_topologicalKrullDim
  | n + 1 => by
      letI : IsIntegral (projectiveContactStage (k := k) n) :=
        instStageIsIntegral (projectiveProductInitial (k := k)) n
      letI : IsIntegral (projectiveContactStage (k := k) (n + 1)) :=
        instStageIsIntegral (projectiveProductInitial (k := k)) (n + 1)
      letI : Nonempty (currentPuncture (k := k) n) :=
        initialPuncture_nonempty ((projectiveProductInitial (k := k)).stage n)
      exact (topologicalKrullDim_eq_of_proper_isomorphism_open
        ((projectiveProductInitial (k := k)).stepProjection n)
        ((projectiveProductInitial (k := k)).stage n).structureMap
        (currentPuncture (k := k) n)).trans (projectiveContactStage_topologicalKrullDim n)

end KltDP.Examples.FrobeniusStageDimension
