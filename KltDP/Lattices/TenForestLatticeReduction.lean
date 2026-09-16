import KltDP.LinearAlgebra.TenForestClassification
import KltDP.Lattices.TenRowNodeSelections

/-!
# The ten-forest lattice reduction from the original source hypotheses

The actual forest classifier is invoked inside the proof. The seven rows
with nonsquare bordered determinant are excluded by the index-square
theorem. D1 and E2 supply their actual four- and three-vertex node sets,
which the characteristic-parity theorem excludes. The conclusion retains
the actual A2 edge pattern and its actual four-node integral half-sum.

The inputs include an actual integral bilinear lattice, a basis witnessing
its unimodularity, actual classes for the vertices and border, equality of
their full Gram matrix, and a characteristic element with the adjunction
pairings. No candidate row, candidate determinant, selected node family,
parity obstruction, or no-even-node theorem is an input. Constructing these lattice and source
inputs geometrically, and excluding the resulting A2 half-sum geometrically,
remain separate obligations.

Reuse: all graph classification, determinant, index and characteristic-code
proofs are existing project results. Pinned Mathlib's finset subtype and
induced-graph APIs, also reviewed in current official Mathlib for the node
selection module, suffice without a source port or dependency change.
-/

namespace KltDP.Lattices.TenForestLatticeReduction

open Matrix SimpleGraph KltDP.Codes KltDP.LinearAlgebra
open SmallADEForestLattice TenRowPicardExclusions TenRowNodeSelections
open scoped BigOperators

variable {Λ V : Type*} [AddCommGroup Λ] [Fintype V] [DecidableEq V]

/-- The original ten-forest source hypotheses, together with an actual
unimodular integral Gram realization and characteristic adjunction, force
the A2 graph and the integral half-sum of its four actual isolated nodes.
This is the lattice reduction, not the geometric no-even-node exclusion. -/
theorem ten_forest_integral_half_sum
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ)
    (hβ : β = 3 ∨ β = 4 ∨ β = 5) (hcard : Fintype.card V = β + 7)
    (hG : G.IsAcyclic)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β)
    (hother : ∀ v, v ≠ C → v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3)
    (hextraCard : (candidateExtraVertices weight C B D).card ≤ 2)
    (hnadjCB : ¬ G.Adj C B) (hnadjCD : ¬ G.Adj C D) (hnadjBD : ¬ G.Adj B D)
    (hseparate : ¬ G.Reachable B D)
    (hdegreeC : G.degree C ≤ 1) (hdegree : ∀ v, G.degree v ≤ 3)
    (hedges : G.edgeFinset.card ≤ β - 1)
    (hboundary : ∃ v, G.Adj C v ∨ G.Adj B v ∨ G.Adj D v)
    (hA : (graphWeightMatrix G (fun v => (weight v : ℚ))).PosDef)
    (hsolve : coeff = (graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
      (fun v => (weight v : ℚ) - 2))
    (hcoeffBounds : ∀ v, 0 ≤ coeff v ∧ coeff v < 1)
    (hvolume : 0 < 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff)
    (hbudget : 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
            threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff)^2)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ) (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = (weight x : ℚ) - 2)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram (graphWeightMatrix G (fun v => (weight v : ℚ)))
        (threeMarkedSource C B D) (-1)) :
    β = 3 ∧ ∃ T u v,
      T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧ u ≠ v ∧
      u ∉ ({C, T, B, D} : Finset V) ∧ v ∉ ({C, T, B, D} : Finset V) ∧
      weight u = 2 ∧ weight v = 2 ∧ G.edgeFinset = {s(C, T), s(u, v)} ∧
      (let S : Finset V := Finset.univ \ {u, v, C, T, B, D}
       S.card = 4 ∧ (∀ x ∈ S, weight x = 2 ∧ ∀ y, ¬ G.Adj x y) ∧
         (borderedGram (graphWeightMatrix G (fun x => (weight x : ℚ)))
           (threeMarkedSource C B D) (-1)).det = 576 ∧
         ∃ m : Λ, (2 : ℤ) • m = (∑ x ∈ S, classes x) ∧
           pairing m m = -2 ∧ pairing K m = 0) := by
  classical
  let w : V → ℚ := fun x => weight x
  let p : V → ℚ := threeMarkedSource C B D
  let A := graphWeightMatrix G w
  let R := borderedGram A p (-1)
  have hnonsquare (hd : |R.det| = 768 ∨ |R.det| = 720 ∨ |R.det| = 972 ∨
      |R.det| = 1728 ∨ |R.det| = 864) : False :=
    bordered_graph_nonsquare_rows_impossible b pairing hunimod classes P G w p hGram hd
  have havoid (fixed : Finset V) (hCF : C ∈ fixed) (hBF : B ∈ fixed)
      (hDF : D ∈ fixed) (x : V) (hx : x ∉ fixed) : x ≠ C ∧ x ≠ B ∧ x ≠ D :=
    ⟨fun h => hx (h.symm ▸ hCF), fun h => hx (h.symm ▸ hBF),
      fun h => hx (h.symm ▸ hDF)⟩
  have hcastRemaining (S : Finset V)
      (hr : ∀ x ∈ S, weight x = 2 ∧ ∀ y, ¬ G.Adj x y) :
      ∀ x ∈ S, w x = 2 ∧ ∀ y, ¬ G.Adj x y := by
    intro x hx
    obtain ⟨hw, hi⟩ := hr x hx
    exact ⟨by simp only [w, hw, Nat.cast_ofNat], hi⟩
  have hclassified := ten_forest_classification G weight coeff C B D β hβ hcard hG
    hC hB hD hother hextraCard hnadjCB hnadjCD hnadjBD hseparate hdegreeC hdegree
    hedges hboundary hA hsolve hcoeffBounds hvolume hbudget hprojection
  rcases hclassified with ⟨h3, T, hTB, hTD, hT, hab⟩ |
    ⟨_, T, _, _, _, hc⟩ |
    ⟨_, T, U, _, _, _, _, _, _, _, hd⟩ |
    ⟨_, T, U, _, _, _, _, _, _, _, he⟩
  · obtain ⟨_, _, hab⟩ := hab
    rcases hab with ⟨_, _, _, _, _, _, _, hb⟩ |
      ⟨u, v, huv, hu, hv, hu2, hv2, hedge, hc, hr, _, _, _, _, hb⟩ |
      ⟨M, _, _, _, _, _, _, _, _, _, _, hb⟩
    · exact (hnonsquare (Or.inl (by
        change |R.det| = 768
        change R.det = 768 at hb
        rw [hb]
        norm_num))).elim
    · let fixed : Finset V := {u, v, C, T, B, D}
      let S : Finset V := Finset.univ \ fixed
      have ha : ∀ x ∈ S, x ≠ C ∧ x ≠ B ∧ x ≠ D := by
        intro x hx
        exact havoid fixed (by simp [fixed]) (by simp [fixed]) (by simp [fixed]) x
          (Finset.mem_sdiff.mp hx).2
      have hh := finset_four_nodes_half b pairing hunimod classes P G w C B D hGram
        (by
          change |R.det| = 576
          change R.det = 576 at hb
          rw [hb]
          norm_num)
        S hc (hcastRemaining S hr) ha K hchar hK
      exact ⟨h3, T, u, v, hTB, hTD, hT, huv, hu, hv, hu2, hv2, hedge, hc, hr, hb, hh⟩
    · exact (hnonsquare (Or.inl (by
        change R.det = 768 at hb
        rw [hb]
        norm_num))).elim
  · obtain ⟨L, M, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb⟩ := hc
    exact (hnonsquare (Or.inr (Or.inl (by
      change R.det = 720 at hb
      rw [hb]
      norm_num)))).elim
  · obtain ⟨M, _, _, _, _, _, _, _, _, _, _, _, _, _, hd⟩ := hd
    rcases hd with ⟨_, hc, hr, _, hb⟩ | ⟨x, y, _, _, _, _, _, _, _, _, _, hb⟩
    · let fixed : Finset V := {C, M, B, D, T, U}
      let S : Finset V := Finset.univ \ fixed
      have ha : ∀ x ∈ S, x ≠ C ∧ x ≠ B ∧ x ≠ D := by
        intro x hx
        exact havoid fixed (by simp [fixed]) (by simp [fixed]) (by simp [fixed]) x
          (Finset.mem_sdiff.mp hx).2
      exact (finset_nodes_determinant1296_impossible b pairing hunimod classes P G w
        C B D hGram (by
          change R.det = 1296 at hb
          change |R.det| = 1296
          rw [hb]
          norm_num) S (Or.inr hc) (hcastRemaining S hr) ha K hchar hK).elim
    · exact (hnonsquare (Or.inr (Or.inr (Or.inl (by
        change R.det = 972 at hb
        rw [hb]
        norm_num))))).elim
  · obtain ⟨M, _, _, hnB, hnM, _, hCiso, hDiso, hTiso, hUiso, _, _, _, hr⟩ := he
    let fixed : Finset V := {C, B, M, D, T, U}
    let Z := G.induce {v | v ∉ fixed}
    obtain ⟨_, _, hZweights, _, hrows⟩ := hr
    rcases hrows with ⟨_, _, hb⟩ | ⟨x, y, _, _, hout, hiso, _, hb⟩ |
      ⟨x, y, z, _, _, _, _, _, _, _, hb⟩ |
      ⟨x, y, z, u, _, _, _, _, _, _, _, _, _, _, hb⟩
    · exact (hnonsquare (Or.inr (Or.inr (Or.inr (Or.inl
        (by
          change R.det = -1728 at hb
          rw [hb]
          norm_num)))))).elim
    · let S : Finset {v | v ∉ fixed} := Finset.univ \ {x, y}
      let nodes : S ↪ V :=
        ⟨fun i => i.val.val, fun i j h => Subtype.ext (Subtype.ext h)⟩
      have hnodesCard : Fintype.card S = 3 := (Fintype.card_coe S).trans hout
      have hnodesIso : ∀ i : S, ∀ j, ¬ G.Adj (nodes i) j := by
        intro i j hadj
        have hi : i.val.val ∉ fixed := i.val.property
        by_cases hj : j ∈ fixed
        · simp only [fixed, Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with hj | hj | hj | hj | hj | hj
          · subst j
            exact hCiso _ hadj.symm
          · subst j
            have hm := (G.mem_neighborFinset B i.val.val).mpr hadj.symm
            rw [hnB, Finset.mem_singleton] at hm
            exact hi (by simp [fixed, hm])
          · subst j
            have hm := (G.mem_neighborFinset M i.val.val).mpr hadj.symm
            rw [hnM, Finset.mem_singleton] at hm
            exact hi (by simp [fixed, hm])
          · subst j
            exact hDiso _ hadj.symm
          · subst j
            exact hTiso _ hadj.symm
          · subst j
            exact hUiso _ hadj.symm
        · exact hiso i.val (Finset.mem_sdiff.mp i.property).2 ⟨j, hj⟩ hadj
      have hnodesWeight : ∀ i : S, w (nodes i) = 2 := fun i => hZweights i.val
      have hnodesContact : ∀ i : S, p (nodes i) = 0 := by
        intro i
        obtain ⟨hiC, hiB, hiD⟩ := havoid fixed (by simp [fixed]) (by simp [fixed])
          (by simp [fixed]) i.val.val i.val.property
        change threeMarkedSource C B D i.val.val = (0 : ℚ)
        simp [threeMarkedSource, Pi.single_apply, hiC, hiB, hiD,
          Ne.symm hiC, Ne.symm hiB, Ne.symm hiD]
      have hnodesK : ∀ i : S, pairing K (classes (nodes i)) = 0 := by
        intro i
        apply Int.cast_injective (α := ℚ)
        have hk := hK (nodes i)
        change (pairing K (classes (nodes i)) : ℚ) = w (nodes i) - 2 at hk
        simpa only [hnodesWeight i, sub_self, Int.cast_zero] using hk
      exact (bordered_graph_determinant1296_impossible b pairing hunimod classes P G w p
        hGram (by
          change R.det = -1296 at hb
          change |R.det| = 1296
          rw [hb]
          norm_num)
        nodes hnodesIso hnodesWeight hnodesContact K hchar hnodesK (Or.inl hnodesCard)).elim
    · exact (hnonsquare (Or.inr (Or.inr (Or.inr (Or.inr
        (by
          change R.det = -864 at hb
          rw [hb]
          norm_num)))))).elim
    · exact (hnonsquare (Or.inr (Or.inr (Or.inl
        (by
          change R.det = -972 at hb
          rw [hb]
          norm_num))))).elim

end KltDP.Lattices.TenForestLatticeReduction
