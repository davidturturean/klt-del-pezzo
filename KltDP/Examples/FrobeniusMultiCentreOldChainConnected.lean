import KltDP.Examples.FrobeniusMultiCentreOldChainGeometry
import Mathlib.Data.Fin.SuccPred
import Mathlib.Topology.Connected.Basic

/-!
# Connectedness of the original old exceptional chain

The original old components are images of the projective line, and consecutive
old components meet by the accepted exceptional-chart geometry. Mathlib's
connected-union theorem applies to their finite ordered family. The original
closed immersion then transfers this connectedness to the reduced old chain.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreOldChain

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
open FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalChainPicard
open FrobeniusMultiCentreChainPicard

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

include ha

/-- Each original old exceptional support is connected and nonempty. -/
theorem oldComponentSupport_isConnected (i : Fin n) (j : Fin q) :
    IsConnected (exceptionalSupport q n a i (Sum.inl j)) := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveLine_isIntegral
  have h := isConnected_range
    (FrobeniusMultiCentreChainPicard.chainCurve q n a ha i j.castSucc).base.hom.continuous
  rw [range_chainCurve, chainMember_castSucc] at h
  exact h

variable [Fact (q + 1).Prime]

/-- The exact old-only support is connected; the newest exceptional curve is
not used as a connector. -/
theorem oldChainSupport_isConnected (i : Fin n) :
    IsConnected (oldChainSupport q n a i) := by
  have hq : 0 < q := by
    have := (Fact.out : (q + 1).Prime).two_le
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  unfold oldChainSupport
  apply IsConnected.iUnion_of_chain
  · exact oldComponentSupport_isConnected (m + 1) n a ha i
  · intro j
    refine Fin.lastCases ?_ (fun l => ?_) j
    · simpa only [Fin.orderSucc_last, Set.inter_self] using
        (oldComponentSupport_isConnected (m + 1) n a ha i (Fin.last m)).nonempty
    · simp only [Fin.orderSucc_castSucc]
      exact exceptionalSupport_adjacent (m + 1) n a ha i l.val (by
        have := l.isLt
        omega)

/-- The constructed original reduced old chain is a connected space. -/
instance oldChain_connectedSpace (i : Fin n) : ConnectedSpace (oldChain q n a ha i) := by
  have hRange : IsConnected (Set.range (oldChainInclusion q n a ha i).base) := by
    rw [range_oldChainInclusion]
    exact oldChainSupport_isConnected q n a ha i
  apply connectedSpace_iff_univ.mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨_, z, _⟩ := hRange.nonempty
    exact ⟨z, Set.mem_univ z⟩
  · apply (oldChainInclusion q n a ha i).isClosedEmbedding.isEmbedding.isInducing.isPreconnected_image.mp
    simpa only [Set.image_univ] using hRange.isPreconnected

/-- Primality forces at least one old component, hence a nonempty old chain. -/
theorem oldChain_nonempty (i : Fin n) : Nonempty (oldChain q n a ha i) :=
  (oldChain_connectedSpace q n a ha i).toNonempty

end KltDP.Examples.FrobeniusMultiCentreOldChain
