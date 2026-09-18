import KltDP.Examples.FrobeniusMultiCentreChainTransversal

/-!
# The original reduced union of the old exceptional components

Inside each accepted full exceptional chain, select the complement of its
last component. The resulting reduced closed subscheme has exactly the
original old exceptional supports, excluding the newest component.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreOldChain

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
open FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalChainPicard
open FrobeniusMultiCentreChainPicard FrobeniusMultiCentreChainTransversal

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- Exactly the old exceptional supports in one original cluster. -/
def oldChainSupport (i : Fin n) : Set (multiSurface (q + 1) n a) :=
  ⋃ j : Fin q, exceptionalSupport q n a i (Sum.inl j)

theorem oldChainSupport_isClosed (i : Fin n) : IsClosed (oldChainSupport q n a i) :=
  isClosed_iUnion_of_finite fun j => exceptionalSupport_isClosed q n a i (Sum.inl j)

variable [IsAlgClosed k] (ha : Function.Injective a)

/-- The accepted irreducible components of the original full chain, in their
original order. -/
def towerComponents (i : Fin n) :
    Fin (q + 1) ≃ ↥(irreducibleComponents (towerChain q n a ha i)) :=
  CurveChain.component (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
    (chainData q n a ha (singlePoints q n a ha) i)

/-- The reduced component subunion obtained by deleting precisely the newest component. -/
abbrev oldChain (i : Fin n) : Scheme.{u} :=
  componentUnionScheme (towerChain q n a ha i) ({towerComponents q n a ha i (Fin.last q)}ᶜ)

/-- Its original closed immersion into the whole multicentre surface. -/
def oldChainInclusion (i : Fin n) : oldChain q n a ha i ⟶ multiSurface (q + 1) n a :=
  componentUnionInclusion (towerChain q n a ha i)
    ({towerComponents q n a ha i (Fin.last q)}ᶜ) ≫ towerChainInclusion q n a ha i

instance oldChainInclusion_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (oldChainInclusion q n a ha i) := by
  unfold oldChainInclusion
  infer_instance

instance oldChain_isReduced (i : Fin n) : AlgebraicGeometry.IsReduced (oldChain q n a ha i) :=
  inferInstanceAs (AlgebraicGeometry.IsReduced (componentUnionScheme _ _))

/-- The accepted component enumeration preserves the original support maps. -/
theorem towerComponents_support (i : Fin n) (j : Fin (q + 1)) :
    (towerComponents q n a ha i j).1 =
      (towerChainInclusion q n a ha i).base ⁻¹'
        exceptionalSupport q n a i (chainMember.{0} q j) := by
  change (CurveChain.component (multiSurface (q + 1) n a) q (chainCurve q n a ha i)
    (chainData q n a ha (singlePoints q n a ha) i) j).1 = _
  rw [CurveChain.component_val, CurveChain.range_curve_eq]
  change (towerChainInclusion q n a ha i).base ⁻¹'
    Set.range (chainCurve q n a ha i j).base = _
  rw [range_chainCurve]

theorem chainMember_castSucc (j : Fin q) : chainMember.{0} q j.castSucc = Sum.inl j := by
  simpa only [Fin.coe_castSucc] using
    chainMember_of_lt q j.castSucc (by simpa only [Fin.coe_castSucc] using j.isLt)

theorem towerComponents_old_support (i : Fin n) (j : Fin q) :
    (towerComponents q n a ha i j.castSucc).1 =
      (towerChainInclusion q n a ha i).base ⁻¹' exceptionalSupport q n a i (Sum.inl j) := by
  rw [towerComponents_support, chainMember_castSucc]

theorem old_support_subset_tower_range (i : Fin n) (j : Fin q) :
    exceptionalSupport q n a i (Sum.inl j) ⊆
      Set.range (towerChainInclusion q n a ha i).base := by
  have h := CurveChain.support_subset_range (multiSurface (q + 1) n a) q
    (chainCurve q n a ha i) j.castSucc
  change Set.range (chainCurve q n a ha i j.castSucc).base ⊆ _ at h
  rw [range_chainCurve, chainMember_castSucc] at h
  exact h

/-- The constructed reduced union has exactly the old exceptional supports
of the original multicentre surface. -/
theorem range_oldChainInclusion (i : Fin n) :
    Set.range (oldChainInclusion q n a ha i).base = oldChainSupport q n a i := by
  let X := towerChain q n a ha i
  let E := towerComponents q n a ha i
  let S : Set ↥(irreducibleComponents X) := {E (Fin.last q)}ᶜ
  have hRange : Set.range (componentUnionInclusion X S).base =
      (componentClosedUnion X S : Set X) := range_componentUnionInclusion X S
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    let w := (componentUnionInclusion X S).base z
    have hw : w ∈ componentClosedUnion X S :=
      (congrArg (fun T : Set X => w ∈ T) hRange).mp ⟨z, rfl⟩
    obtain ⟨C, hC, hxC⟩ := (mem_componentClosedUnion X S w).mp hw
    obtain ⟨r, rfl⟩ := E.surjective C
    have hr : r ≠ Fin.last q := fun h => hC (Set.mem_singleton_iff.mpr (congrArg E h))
    have hrl : r.val < q := by
      have := r.isLt
      have hrv : r.val ≠ q := fun h => hr (Fin.ext h)
      omega
    let j : Fin q := ⟨r.val, hrl⟩
    have hrj : r = j.castSucc := Fin.ext rfl
    change w ∈ (towerComponents q n a ha i r).1 at hxC
    rw [hrj, towerComponents_old_support] at hxC
    exact Set.mem_iUnion.mpr ⟨j, hxC⟩
  · intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨w, hw⟩ := old_support_subset_tower_range q n a ha i j hj
    have hwC : w ∈ (towerComponents q n a ha i j.castSucc).1 := by
      rw [towerComponents_old_support]
      exact (show (towerChainInclusion q n a ha i).base w ∈
        exceptionalSupport q n a i (Sum.inl j) from hw.symm ▸ hj)
    have hwS : w ∈ componentClosedUnion X S := by
      apply (mem_componentClosedUnion X S w).mpr
      refine ⟨E j.castSucc, ?_, hwC⟩
      intro h
      have he := E.injective (Set.mem_singleton_iff.mp h)
      have hv := congrArg Fin.val he
      simp only [Fin.coe_castSucc, Fin.val_last] at hv
      exact (Nat.ne_of_lt j.isLt) hv
    have hwRange : w ∈ Set.range (componentUnionInclusion X S).base :=
      hRange.symm ▸ (show w ∈ (componentClosedUnion X S : Set X) from hwS)
    obtain ⟨z, hz⟩ := hwRange
    refine ⟨z, ?_⟩
    change (towerChainInclusion q n a ha i).base ((componentUnionInclusion X S).base z) = x
    rw [hz, hw]

end KltDP.Examples.FrobeniusMultiCentreOldChain
