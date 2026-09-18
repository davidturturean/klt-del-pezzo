import KltDP.Geometry.RationalTreePicardChainOfCurves
import KltDP.Geometry.RationalTreePicardExponentTransfer

/-!
# Removing the last component of an original rational chain

The original chain incidences make its last component a leaf. The accepted
leaf-inheritance and component-restriction theorems therefore give the
degree-zero clause on the reduced complementary union. No new nodal gluing
or transversality construction is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u}) [NoetherianSpace X]
  (m : ℕ) (e : Fin (m + 1) ≃ ↥(irreducibleComponents X)) (hc : IsChain X e)
include hc

/-- The last component of a non-singleton chain meets the remaining union
in its original final chain point. -/
theorem chainLast_complement_inter (hm : 0 < m) :
    ∃ x : X, (e (Fin.last m)).1 ∩
      (componentClosedUnion X ({e (Fin.last m)}ᶜ) : Set X) = {x} := by
  let j : Fin m := ⟨m - 1, by omega⟩
  have hj : j.succ = Fin.last m := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    dsimp [j]
    omega
  refine ⟨chainPoint X e hc j, ?_⟩
  rw [← chain_inter_eq X e hc j, hj]
  ext x
  constructor
  · rintro ⟨hxlast, hxrest⟩
    obtain ⟨C, hC, hxC⟩ := (mem_componentClosedUnion X _ x).mp hxrest
    obtain ⟨r, rfl⟩ := e.surjective C
    have hr : r ≠ Fin.last m := fun h => hC (by simp only [Set.mem_singleton_iff]; rw [h])
    have hrl : r.val < m := by
      have := r.isLt
      have hrv : r.val ≠ m := fun h => hr (Fin.ext h)
      omega
    have hre : r = j.castSucc := by
      apply Fin.ext
      simp only [Fin.coe_castSucc]
      dsimp [j]
      by_contra h
      have hd := hc.disjoint r (Fin.last m) (by simp only [Fin.val_last]; omega)
      exact Set.disjoint_left.mp hd hxC hxlast
    rw [hre] at hxC
    exact ⟨hxC, hxlast⟩
  · rintro ⟨hxj, hxlast⟩
    refine ⟨hxlast, (mem_componentClosedUnion X _ x).mpr ⟨e j.castSucc, ?_, hxj⟩⟩
    intro h
    have he := e.injective (Set.mem_singleton_iff.mp h)
    have hv := congrArg Fin.val he
    simp only [Fin.coe_castSucc, Fin.val_last] at hv
    exact (Nat.ne_of_lt j.isLt) hv

variable [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]

/-- Deleting the actual last component retains the proved tree and transverse
branch properties. -/
theorem chainLast_complement_geometry (hm : 0 < m)
    (hdim : topologicalKrullDim X ≤ 1)
    (ht : HasTransverseComponentBranches X) :
    (componentPointIncidenceGraph (componentUnionScheme X ({e (Fin.last m)}ᶜ))).IsTree ∧
      HasTransverseComponentBranches (componentUnionScheme X ({e (Fin.last m)}ᶜ)) := by
  obtain ⟨x, hx⟩ := chainLast_complement_inter X m e hc hm
  exact inheritsLeafHypotheses X (e (Fin.last m)) x hx hdim (isTree_of_chain X e hc) ht

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Zero component degrees on all components except the last trivialize the
restriction to precisely their reduced union. -/
theorem chainLast_complement_trivial_of_degree_zero (hm : 0 < m)
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) (ht : HasTransverseComponentBranches X)
    (E : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (L : InvertibleSheaf X)
    (hL : ∀ C : ↥(irreducibleComponents X), C ≠ e (Fin.last m) →
      componentExponent k X {C} (E C) L = 0) :
    Nonempty ((schemeModulePullback (componentUnionInclusion X ({e (Fin.last m)}ᶜ))).obj
      L.obj ≅ _root_.SheafOfModules.unit
        (componentUnionScheme X ({e (Fin.last m)}ᶜ)).ringCatSheaf) := by
  obtain ⟨hTree, htrans⟩ := chainLast_complement_geometry X m e hc hm hdim ht
  let S : Set ↥(irreducibleComponents X) := {e (Fin.last m)}ᶜ
  let ident := componentUnionIdentification X S
  refine KltDP.Manuscript.S02.rationalTreePicard_trivial_of_degree_zero
    (componentUnionScheme X S) (componentUnionInclusion X S ≫ f)
    (componentUnionScheme_topologicalKrullDim_le_one X S hdim) hTree htrans
    (ident.projectiveLineIso E) (componentUnionRestriction X S L) (fun C => ?_)
  rw [componentExponent_componentUnionRestriction k S ident E L C]
  exact hL _ (by
    have hC := componentImage_mem X S C
    exact fun h => hC (Set.mem_singleton_iff.mpr h))

end KltDP.Geometry.RationalTreePicard
