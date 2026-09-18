import KltDP.Manuscript.S01.Examples
import KltDP.Manuscript.Datum.AnticanonicalDegrees
import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceCanonicalClassification
import KltDP.Geometry.FrobeniusTargetIntrinsicDelPezzoIff
import KltDP.Geometry.FrobeniusExactSingularCount
import KltDP.Geometry.RationalWeilCartierRestrictionDegree
import KltDP.Examples.FrobeniusDiscrepancyWitness
import KltDP.Examples.FrobeniusDiscrepancyBounds
import KltDP.Examples.FrobeniusMultiCentreContractingNullLocus
import KltDP.Examples.FrobeniusMultiCentreContractingBig
import KltDP.Examples.FrobeniusMultiCentreNullCurveClassification
import KltDP.Examples.FrobeniusMultiCentreRealizedCurveClasses
import KltDP.Examples.FrobeniusGraphFiberDisjointSPn
import KltDP.Examples.FrobeniusMultiCentreFiberContacts
import KltDP.Examples.FrobeniusMultiCentreGraphContacts
import KltDP.Examples.FrobeniusTargetCanonicalPullbackClass
import KltDP.Examples.FrobeniusMultiCentreTargetQCartier

/-!
# Proposition 10.1 (`prop:frobenius-family`, manuscript lines 2892–2996):
# canonical divisors in the Frobenius family

For every prime `p = q + 1`, every algebraically closed field of characteristic `p`, and every
`n ≥ 3`, the union's multi-centre Frobenius construction `π : S_{p,n} → X_{p,n}`
(`sourceSurface q n a ha _`, the contraction of the union's existence theorem) is analysed:

* the `1 + n + nq` contracted curves `B, F_i, C_{ij}` (`retainedCurve`) have the manuscript's
  classes `B = pa + b - ΣE_{ij}`, `F_i = b - Σ_j E_{ij}`, `C_{ij} = E_{ij} - E_{i,j+1}` (as
  realizations of the union's integral vectors `graphVector, fiberVector, chainVector`), the
  intersection matrix `gram` (one isolated curve of square `-p(n-2)`, `n` isolated curves of
  square `-p`, `n` chains `A_{p-1}` of `(-2)`-curves), and distinct blocks are disjoint;
* they are exactly the exceptional curves of `π`; `P_i = E_{ip}` is exterior with
  `B·P_i = F_i·P_i = C_{i,p-1}·P_i = 1`;
* `M = B + (n-2)b` (the union's `contractingDivisor`) is nef and big with exact null locus the
  reduced divisor `D`, `M² = p(n-2)`;
* `L = π^*(-K_X) ∼_ℚ t M`, `L·P_i = t`, with `t = d/(p(n-2))`, `d = 2 - (p-2)(n-2)`;
* the discrepancy `K_S - π^*K_X` has coefficients `-(1 - 2/(p(n-2)))` on `B`, `-(1 - 2/p)` on
  `F_i` and `0` on `C_{ij}` (the manuscript's `λ_B, λ_F, 0`);
* `X_{p,n}` is normal klt with `ρ = 1` and `2n+1` singular points; `-K_X` is ample iff `p = 2` or
  `(p,n) = (3,3)`, `K_X ∼_ℚ 0` iff `(p,n) = (3,4)`, and `K_X` is ample otherwise;
* in the del Pezzo cases `L² = d²/(p(n-2))` for the resolution datum.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Examples KltDP.Examples.FrobeniusMultiCentreSurface
open KltDP.Examples.FrobeniusMultiCentreIntegral KltDP.Examples.FrobeniusProjectivityProved
open KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
open KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives
open KltDP.Examples.FrobeniusMultiCentreContractingNef
open KltDP.Examples.FrobeniusMultiCentreContractingClass
open KltDP.Examples.FrobeniusMultiCentreExceptionalPrime
open KltDP.Examples.FrobeniusMultiCentreSpecialNullCurves
open KltDP.Examples.FrobeniusMultiCentreExceptional
open KltDP.Examples.FrobeniusMultiCentreExceptionalGlobalClasses
open KltDP.Examples.FrobeniusMultiCentreGraphFiber
open KltDP.Examples.FrobeniusMultiCentrePicardRealization
open KltDP.Examples.FrobeniusMultiCentreRealizedCurveClasses
open KltDP.Examples.FrobeniusMultiCentreGraphExceptionalPairing
open KltDP.Geometry.PrimeCurveClassPairing
open KltDP.Geometry.InvertibleSheafSectionPowers
open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

universe u

namespace KltDP.Manuscript.S10

open KltDP.Manuscript

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

/-! ### Labels and the manuscript's intersection matrix -/

/-- Labels of the `1 + n + nq` contracted curves: `B` (`inl`), `F_i` (`inr (inl i)`) and the chain
members `C_{ij}` (`inr (inr (i, j))`, `j : Fin q`, `C_{ij} = E_{ij} - E_{i,j+1}`). -/
abbrev RetainedLabel (q n : ℕ) := Unit ⊕ Fin n ⊕ (Fin n × Fin q)

/-- The block (connected component of `D`) of a label: `B`, `F_i`, or the `i`-th chain. -/
def block {q n : ℕ} : RetainedLabel q n → Unit ⊕ Fin n ⊕ Fin n
  | .inl _ => .inl ()
  | .inr (.inl i) => .inr (.inl i)
  | .inr (.inr (i, _)) => .inr (.inr i)

/-- The manuscript's intersection matrix of `D = B + Σ_i (F_i + Σ_j C_{ij})`: `B² = -p(n-2)`,
`F_i² = -p`, the `i`-th chain is an `A_{p-1}` chain of `(-2)`-curves (`C_{ij}·C_{i,j+1} = 1`), and
all other entries vanish. -/
def gram (q n : ℕ) : RetainedLabel q n → RetainedLabel q n → ℤ
  | .inl _, .inl _ => -((q + 1 : ℕ) : ℤ) * ((n : ℤ) - 2)
  | .inr (.inl i), .inr (.inl i') => if i = i' then -((q + 1 : ℕ) : ℤ) else 0
  | .inr (.inr (i, j)), .inr (.inr (i', j')) =>
      if i = i' then
        (if j = j' then -2 else if j.val + 1 = j'.val ∨ j'.val + 1 = j.val then 1 else 0)
      else 0
  | _, _ => 0

/-- The intersection numbers of the contracted curves with the exterior curve `P_i = E_{ip}`:
`B·P_i = 1`, `F_{i'}·P_i = [i' = i]`, `C_{i'j}·P_i = [i' = i ∧ j = p-1]`. -/
def newestGram (q n : ℕ) : RetainedLabel q n → Fin n → ℤ
  | .inl _, _ => 1
  | .inr (.inl i'), i => if i' = i then 1 else 0
  | .inr (.inr (i', j)), i => if i' = i ∧ j.val + 1 = q then 1 else 0

theorem retainedLabel_card (q n : ℕ) : Fintype.card (RetainedLabel q n) = 1 + n + n * q := by
  simp only [RetainedLabel, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
    Fintype.card_prod]
  ring

/-! ### The manuscript's integral classes -/

/-- The manuscript's classes in the total-transform basis `(a, b, E_{ij})`:
`B = pa + b - ΣE_{ij}`, `F_i = b - Σ_j E_{ij}`, `C_{ij} = E_{ij} - E_{i,j+1}`. -/
def retainedVector (q n : ℕ) : RetainedLabel q n → FrobeniusPicard.PicardVector (q + 1) n
  | .inl _ => FrobeniusPicard.graphVector (q + 1) n
  | .inr (.inl i) => FrobeniusPicard.fiberVector (q + 1) n i
  | .inr (.inr (i, j)) => FrobeniusPicard.chainVector (q + 1) n i j.castSucc
      (by simpa only [Fin.coe_castSucc] using Nat.succ_lt_succ j.isLt)

theorem retainedVector_pairing (q n : ℕ) (l l' : RetainedLabel q n) :
    FrobeniusPicard.pairing (retainedVector q n l) (retainedVector q n l') = gram q n l l' := by
  rcases l with _ | (i | ⟨i, j⟩) <;> rcases l' with _ | (i' | ⟨i', j'⟩)
  · simp [retainedVector, gram, FrobeniusPicard.graph_square]
  · simp [retainedVector, gram, FrobeniusPicard.pairing_graph_fiber]
  · simp [retainedVector, gram, FrobeniusPicard.pairing_comm _ (FrobeniusPicard.chainVector _ _ _ _ _),
      FrobeniusPicard.pairing_chain_graph]
  · simp [retainedVector, gram, FrobeniusPicard.pairing_comm _ (FrobeniusPicard.graphVector _ _),
      FrobeniusPicard.pairing_graph_fiber]
  · simp [retainedVector, gram, FrobeniusPicard.pairing_fibers]
  · simp [retainedVector, gram, FrobeniusPicard.pairing_comm _ (FrobeniusPicard.chainVector _ _ _ _ _),
      FrobeniusPicard.pairing_chain_fiber]
  · simp [retainedVector, gram, FrobeniusPicard.pairing_chain_graph]
  · simp [retainedVector, gram, FrobeniusPicard.pairing_chain_fiber]
  · simp [retainedVector, gram, FrobeniusPicard.pairing_chains, Fin.castSucc_inj]

theorem retainedVector_newest_pairing (q n : ℕ) (l : RetainedLabel q n) (i : Fin n) :
    FrobeniusPicard.pairing (retainedVector q n l) (FrobeniusPicard.exceptional (i, Fin.last q)) =
      newestGram q n l i := by
  rcases l with _ | (i' | ⟨i', j⟩)
  · simp [retainedVector, newestGram, FrobeniusPicard.pairing_graph_exceptional]
  · simp [retainedVector, newestGram, FrobeniusPicard.pairing_fiber_exceptional, @eq_comm _ i' i]
  · simp only [retainedVector, newestGram, FrobeniusPicard.chainVector,
      FrobeniusPicard.pairing_difference_left, FrobeniusPicard.exceptional, Prod.mk.injEq,
      Fin.ext_iff, Fin.coe_castSucc, Fin.val_last]
    have hj : j.val ≠ q := Nat.ne_of_lt j.isLt
    by_cases hi : (i' : ℕ) = i
    · have hi' : i' = i := Fin.ext hi
      subst hi'
      by_cases hjq : j.val + 1 = q
      · simp [hjq, hj]
      · simp [hjq, hj]
    · simp [hi]

/-! ### The universal section: an arbitrary contraction of the Frobenius surface -/

section Universal

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- The contracted prime curves of the source surface `S_{p,n}`, indexed by `RetainedLabel`. -/
def retainedCurve : RetainedLabel q n →
    (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve
  | .inl _ => graphPrimeCurve q n a ha (originalMultiStructureProjective k (q + 1) n a)
  | .inr (.inl i) => fiberPrimeCurve q n a ha (originalMultiStructureProjective k (q + 1) n a) i
  | .inr (.inr (i, j)) =>
      exceptionalPrimeCurveSPn q n a ha i (.inl j) (originalMultiStructureProjective k (q + 1) n a)

/-- The exterior curve `P_i = E_{ip}`. -/
abbrev newestCurveP (i : Fin n) :
    (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve :=
  exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) (originalMultiStructureProjective k (q + 1) n a)

/-- Regularity of the source surface. -/
abbrev sourceRegular :
    ∀ x : (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).Point,
      RegularPoint (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).toScheme x :=
  multiSurfaceSurface_regularPoints (q + 1) n a ha (originalMultiStructureProjective k (q + 1) n a)

/-- The Cartier class of each contracted curve is the realization of the manuscript's vector. -/
theorem retainedCurve_cartierClass (l : RetainedLabel q n) :
    cartierPicardHom (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).toScheme
      ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).primeCurveCartier
        (sourceRegular q n a ha) (retainedCurve q n a ha l)) =
      realization q n a (retainedVector q n l) := by
  rcases l with _ | (i | ⟨i, j⟩)
  · rw [retainedCurve, retainedVector, graphPrimeCurve_cartierClass, realization_graphVector]
  · rw [retainedCurve, retainedVector, realization_fiberVector]
    exact fiberCartier_picard q n a ha (originalMultiStructureProjective k (q + 1) n a) i
  · rw [retainedCurve, retainedVector, realization_chainVector]
    letI := exceptionalCurve_isIntegral q n a ha i (.inl j)
    exact PrimeCurveTransversalPoint.cartierPicardHom_primeCurveCartier_of_kernel
      (sourceRegular q n a ha) _ (exceptionalCurveι q n a i (.inl j)) rfl
      (exceptionalKernelLine q n a ha i (.inl j)) rfl

omit [Fact (q + 1).Prime] [CharP k (q + 1)] in
/-- The Cartier class of `P_i` is `E_{ip}` (the last total transform). -/
theorem newestCurveP_cartierClass (i : Fin n) :
    cartierPicardHom (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).toScheme
      ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).primeCurveCartier
        (sourceRegular q n a ha) (newestCurveP q n a ha i)) =
      realization q n a (FrobeniusPicard.exceptional (i, Fin.last q)) := by
  rw [realization_exceptional, ← newestClass_SPn q n a ha i]
  letI := exceptionalCurve_isIntegral q n a ha i (.inr PUnit.unit)
  exact PrimeCurveTransversalPoint.cartierPicardHom_primeCurveCartier_of_kernel
    (sourceRegular q n a ha) _ (exceptionalCurveι q n a i (.inr PUnit.unit)) rfl
    (exceptionalKernelLine q n a ha i (.inr PUnit.unit)) rfl

/-- The intersection matrix of the contracted curves is the manuscript's `gram`. -/
theorem retainedCurve_intersectionNumber (l l' : RetainedLabel q n) :
    (retainedCurve q n a ha l).intersectionNumber
      ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).primeCurveCartier
        (sourceRegular q n a ha) (retainedCurve q n a ha l')) = gram q n l l' := by
  rw [← PrimeCurve.picardRestrictionDegreeHom_cartierPicardHom, ← pairing_primeCurve_left,
    retainedCurve_cartierClass, retainedCurve_cartierClass, ← retainedVector_pairing]
  exact realization_preserves_pairing q n a ha (originalMultiStructureProjective k (q + 1) n a) _ _

/-- The intersection numbers with the exterior curves `P_i`. -/
theorem retainedCurve_newest_intersectionNumber (l : RetainedLabel q n) (i : Fin n) :
    (retainedCurve q n a ha l).intersectionNumber
      ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).primeCurveCartier
        (sourceRegular q n a ha) (newestCurveP q n a ha i)) = newestGram q n l i := by
  rw [← PrimeCurve.picardRestrictionDegreeHom_cartierPicardHom, ← pairing_primeCurve_left,
    retainedCurve_cartierClass, newestCurveP_cartierClass, ← retainedVector_newest_pairing]
  exact realization_preserves_pairing q n a ha (originalMultiStructureProjective k (q + 1) n a) _ _

/-- `P_i` is a `(-1)`-curve and distinct `P_i` are orthogonal. -/
theorem newestCurveP_intersectionNumber (i i' : Fin n) :
    (newestCurveP q n a ha i).intersectionNumber
      ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).primeCurveCartier
        (sourceRegular q n a ha) (newestCurveP q n a ha i')) = if i = i' then -1 else 0 := by
  rw [← PrimeCurve.picardRestrictionDegreeHom_cartierPicardHom, ← pairing_primeCurve_left,
    newestCurveP_cartierClass, newestCurveP_cartierClass]
  rw [show (pairing (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
      (sourceRegular q n a ha) (realization q n a (FrobeniusPicard.exceptional (i, Fin.last q)))
      (realization q n a (FrobeniusPicard.exceptional (i', Fin.last q)))) =
      FrobeniusPicard.pairing (FrobeniusPicard.exceptional (i, Fin.last q))
        (FrobeniusPicard.exceptional (i', Fin.last q)) from
    realization_preserves_pairing q n a ha (originalMultiStructureProjective k (q + 1) n a) _ _]
  rw [FrobeniusPicard.pairing_exceptional]
  simp

/-- Labels represent distinct prime curves (for `n > 2`, so that `B² ≠ 0`). -/
theorem retainedCurve_injective (hn : 2 < n) : Function.Injective (retainedCurve q n a ha) := by
  intro l l' h
  have hg : gram q n l' l' = gram q n l l' := by
    rw [← retainedCurve_intersectionNumber q n a ha l' l',
      ← retainedCurve_intersectionNumber q n a ha l l', h]
  have hp : (1 : ℤ) ≤ ((q + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos q
  have hpos : (0 : ℤ) < ((q + 1 : ℕ) : ℤ) * ((n : ℤ) - 2) :=
    mul_pos (by omega) (by omega)
  by_contra hne
  rcases l with _ | (i | ⟨i, j⟩) <;> rcases l' with _ | (i' | ⟨i', j'⟩)
  · exact hne rfl
  · change (if i' = i' then -((q + 1 : ℕ) : ℤ) else 0) = 0 at hg
    rw [if_pos rfl] at hg
    omega
  · change (if i' = i' then (if j' = j' then (-2 : ℤ) else
      if j'.val + 1 = j'.val ∨ j'.val + 1 = j'.val then 1 else 0) else 0) = 0 at hg
    rw [if_pos rfl, if_pos rfl] at hg
    omega
  · change -((q + 1 : ℕ) : ℤ) * ((n : ℤ) - 2) = 0 at hg
    linarith
  · have hii' : i ≠ i' := fun h' => hne (by rw [h'])
    change (if i' = i' then -((q + 1 : ℕ) : ℤ) else 0) =
      (if i = i' then -((q + 1 : ℕ) : ℤ) else 0) at hg
    rw [if_pos rfl, if_neg hii'] at hg
    omega
  · change (if i' = i' then (if j' = j' then (-2 : ℤ) else
      if j'.val + 1 = j'.val ∨ j'.val + 1 = j'.val then 1 else 0) else 0) = 0 at hg
    rw [if_pos rfl, if_pos rfl] at hg
    omega
  · change -((q + 1 : ℕ) : ℤ) * ((n : ℤ) - 2) = 0 at hg
    linarith
  · change (if i' = i' then -((q + 1 : ℕ) : ℤ) else 0) = 0 at hg
    rw [if_pos rfl] at hg
    omega
  · change (if i' = i' then (if j' = j' then (-2 : ℤ) else
        if j'.val + 1 = j'.val ∨ j'.val + 1 = j'.val then 1 else 0) else 0) =
      (if i = i' then (if j = j' then (-2 : ℤ) else
        if j.val + 1 = j'.val ∨ j'.val + 1 = j.val then 1 else 0) else 0) at hg
    rw [if_pos rfl, if_pos rfl] at hg
    by_cases hii' : i = i'
    · subst hii'
      have hjj' : j ≠ j' := fun h' => hne (by rw [h'])
      rw [if_pos rfl, if_neg hjj'] at hg
      by_cases hadj : j.val + 1 = j'.val ∨ j'.val + 1 = j.val
      · rw [if_pos hadj] at hg
        omega
      · rw [if_neg hadj] at hg
        omega
    · rw [if_neg hii'] at hg
      omega

/-- Distinct blocks of `D` have disjoint supports. -/
theorem retainedCurve_disjoint (l l' : RetainedLabel q n) (hll' : block l ≠ block l') :
    Disjoint (retainedCurve q n a ha l :
        Set (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).toScheme)
      (retainedCurve q n a ha l' :
        Set (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).toScheme) := by
  rcases l with _ | (i | ⟨i, j⟩) <;> rcases l' with _ | (i' | ⟨i', j'⟩)
  · exact absurd rfl hll'
  · exact FrobeniusGraphFiberDisjointSPn.graphStrict_fiberStrict_disjoint' q n a i'
  · exact FrobeniusMultiCentreGraphContacts.graphStrict_disjoint_exceptional_same q n a i' j'
  · exact (FrobeniusGraphFiberDisjointSPn.graphStrict_fiberStrict_disjoint' q n a i).symm
  · have hii' : i ≠ i' := fun h => hll' (by subst h; rfl)
    exact fiberStrict_disjoint (q + 1) n a ha hii'
  · by_cases hii' : i = i'
    · subst hii'
      exact FrobeniusMultiCentreFiberContacts.fiberStrict_disjoint_exceptional_same q n a i j'
    · exact fiberStrict_disjoint_exceptional q n a ha hii' (.inl j')
  · exact (FrobeniusMultiCentreGraphContacts.graphStrict_disjoint_exceptional_same q n a i j).symm
  · by_cases hii' : i' = i
    · subst hii'
      exact (FrobeniusMultiCentreFiberContacts.fiberStrict_disjoint_exceptional_same q n a i' j).symm
    · exact (fiberStrict_disjoint_exceptional q n a ha hii' (.inl j)).symm
  · have hii' : i ≠ i' := fun h => hll' (by subst h; rfl)
    exact exceptionalSupport_disjoint_of_ne q n a ha hii' _ _

/-- The reduced divisor `D` of the manuscript is the union of the contracted curves. -/
theorem contractingSupport_eq_iUnion :
    FrobeniusMultiCentreContractingNullLocus.contractingSupport q n a ha
        (originalMultiStructureProjective k (q + 1) n a) =
      ⋃ l : RetainedLabel q n, (retainedCurve q n a ha l :
        Set (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).toScheme) := by
  ext x
  simp only [FrobeniusMultiCentreContractingNullLocus.contractingSupport, Set.mem_union,
    Set.mem_iUnion]
  constructor
  · rintro ((hx | ⟨i, hx⟩) | ⟨i, j, hx⟩)
    · exact ⟨.inl (), hx⟩
    · exact ⟨.inr (.inl i), hx⟩
    · exact ⟨.inr (.inr (i, j)), hx⟩
  · rintro ⟨l, hx⟩
    rcases l with _ | (i | ⟨i, j⟩)
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr ⟨i, hx⟩)
    · exact Or.inr ⟨i, j, hx⟩

variable (hn : 2 < n) (Y : NormalProjectiveSurface k)
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme)
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0)

include hn hπ hcriterion in
/-- The exceptional curves of the contraction are exactly the `1 + n + nq` curves of `D`. -/
theorem isExceptionalCurve_iff_retained
    (C : (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve) :
    IsExceptionalCurve π C ↔ ∃ l : RetainedLabel q n, C = retainedCurve q n a ha l := by
  constructor
  · intro hC
    have hzero : C.restrictionDegree (originalLine q n a ha) = 0 :=
      (hcriterion C).mp (IsExceptionalCurve.exists_fieldPoint_factor π hπ C hC)
    rcases (FrobeniusMultiCentreNullCurveClassification.restrictionDegree_eq_zero_iff q n a ha
        (originalMultiStructureProjective k (q + 1) n a) hn C).mp hzero with h | ⟨i, h⟩ | ⟨i, j, h⟩
    · exact ⟨.inl (), h⟩
    · exact ⟨.inr (.inl i), h⟩
    · exact ⟨.inr (.inr (i, j)), h⟩
  · rintro ⟨l, rfl⟩
    have hzero : (retainedCurve q n a ha l).restrictionDegree (originalLine q n a ha) = 0 := by
      apply (FrobeniusMultiCentreNullCurveClassification.restrictionDegree_eq_zero_iff q n a ha
        (originalMultiStructureProjective k (q + 1) n a) hn _).mpr
      rcases l with _ | (i | ⟨i, j⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨i, rfl⟩)
      · exact Or.inr (Or.inr ⟨i, j, rfl⟩)
    obtain ⟨p, hp, -⟩ := (hcriterion _).mpr hzero
    exact IsExceptionalCurve.of_fieldPoint_factor π _ p hp

/-- `M · P_i = 1` (integral restriction degree of `M` on `P_i`). -/
theorem originalLine_newestCurveP_degree (i : Fin n) :
    (newestCurveP q n a ha i).restrictionDegree (originalLine q n a ha) = 1 := by
  have h1 : (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).picardRestrictionDegreeHom
      (newestCurveP q n a ha i) (contractingClass q n a ha) = 1 := by
    rw [← pairing_primeCurve_right _ (sourceRegular q n a ha), newestCurveP_cartierClass,
      realization_exceptional, ← newestClass_SPn q n a ha i]
    exact contractingClass_newest_pairing q n a ha (originalMultiStructureProjective k (q + 1) n a) i
  rw [← contractingLine_class q n a ha (originalMultiStructureProjective k (q + 1) n a)] at h1
  change (newestCurveP q n a ha i).picardRestrictionDegree
    (contractingLine q n a ha (originalMultiStructureProjective k (q + 1) n a)).toPic = 1 at h1
  rwa [PrimeCurve.picardRestrictionDegree_toPic] at h1

include hπ hcriterion in
/-- `P_i` is exterior (not contracted). -/
theorem newestCurveP_not_exceptional (i : Fin n) :
    ¬ IsExceptionalCurve π (newestCurveP q n a ha i) := by
  intro hC
  have hzero := (hcriterion _).mp (IsExceptionalCurve.exists_fieldPoint_factor π hπ _ hC)
  rw [originalLine_newestCurveP_degree] at hzero
  exact one_ne_zero hzero

variable [IsProper π] [Surjective π] [IsIso π.c]
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj)

include hn hπ hbir hconnected hcriterion hm e in
/-- `L = π^*(-K_X) ∼_ℚ t M` with `t = d/(p(n-2))`, `d = 2 - (p-2)(n-2)`. -/
theorem anticanonical_pullback_classMap
    (hK : Y.QCartier (rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion))) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilClassMap
        (-QCartierPullback.pullback
          (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := Y) π
          (rationalizeWeilDivisor Y
            (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) hK) =
      ((2 - (((q + 1 : ℕ) : ℚ) - 2) * ((n : ℚ) - 2)) / (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2))) •
        (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilClassMap
          ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalCartierToWeilHom
            (contractingDivisor q n a ha (originalMultiStructureProjective k (q + 1) n a))) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  have h := FrobeniusTargetCanonicalPullbackClass.target_canonical_pullback_class
    q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hK
  rw [map_neg, h, ← neg_smul]
  refine congrArg₂ (fun (c : ℚ) v => c • v) ?_ rfl
  push_cast
  ring

include hn hπ hbir hconnected hcriterion hm e in
/-- `L · P_i = t`. -/
theorem anticanonical_pullback_newest_degree
    (hK : Y.QCartier (rationalizeWeilDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion))) (i : Fin n) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalPicardRestrictionDegree
        (newestCurveP q n a ha i)
        ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilToRationalPicard
          (sourceRegular q n a ha)
          (-QCartierPullback.pullback
            (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := Y) π
            (rationalizeWeilDivisor Y
              (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) hK)) =
      (2 - (((q + 1 : ℕ) : ℚ) - 2) * ((n : ℚ) - 2)) / (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2)) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  rw [(sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalRestrictionDegree_of_class_eq_smul_cartier
    (sourceRegular q n a ha) _ (contractingDivisor q n a ha (originalMultiStructureProjective k (q + 1) n a)) _
    (anticanonical_pullback_classMap q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hK)]
  have h1 := originalLine_newestCurveP_degree q n a ha i
  change (newestCurveP q n a ha i).restrictionDegree
    (cartierDivisorInvertibleSheaf _ (contractingDivisor q n a ha (originalMultiStructureProjective k (q + 1) n a))) = 1 at h1
  rw [h1]
  simp

include hn hπ hbir hconnected hcriterion hm e in
/-- The discrepancy `K_S - π^*K_X` (for an actual canonical Cartier divisor `D = K_S` pushing
forward to `K_X`) has coefficients `-(1 - 2/(p(n-2)))` on `B`, `-(1 - 2/p)` on every `F_i`, and
`0` on every chain member `C_{ij}`; i.e. `π^*K_X = K_S + λ_B B + λ_F Σ F_i` with the
manuscript's `λ_B = 1 - 2/(p(n-2))`, `λ_F = 1 - 2/p`. -/
theorem discrepancy_coefficients :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    ∃ (D : CartierDivisor (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).toScheme)
      (hK : Y.QCartier (rationalizeWeilDivisor Y
        (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion))),
      Nonempty (cartierDivisorModule (sourceSurface q n a ha
          (originalMultiStructureProjective k (q + 1) n a)).toScheme D ≅
        relativeDifferentialExterior (multiStructure (q + 1) n a) 2) ∧
      BirationalWeilPushforward.pushforward
          (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (X := Y)
          π hbir ((sourceSurface q n a ha
            (originalMultiStructureProjective k (q + 1) n a)).cartierToWeilHom D) =
        targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion ∧
      ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalCartierToWeilHom D -
          QCartierPullback.pullback
            (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := Y) π
            (rationalizeWeilDivisor Y
              (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) hK)
          (retainedCurve q n a ha (.inl ())) =
        -(1 - 2 / (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2))) ∧
      (∀ i : Fin n,
        ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalCartierToWeilHom D -
          QCartierPullback.pullback
            (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := Y) π
            (rationalizeWeilDivisor Y
              (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) hK)
          (retainedCurve q n a ha (.inr (.inl i))) = -(1 - 2 / ((q + 1 : ℕ) : ℚ))) ∧
      (∀ (i : Fin n) (j : Fin q),
        ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalCartierToWeilHom D -
          QCartierPullback.pullback
            (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := Y) π
            (rationalizeWeilDivisor Y
              (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion)) hK)
          (retainedCurve q n a ha (.inr (.inr (i, j)))) = 0) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨D, hK, hiso, hpush, hΔ, -, -⟩ :=
    FrobeniusDiscrepancyWitness.exists_discrepancy_witness
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  try dsimp only at hΔ
  have hp0 : ((q + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero q)
  have hr0 : ((n : ℚ) - 2) ≠ 0 := by
    have h2n : (2 : ℚ) < n := by exact_mod_cast hn
    exact ne_of_gt (sub_pos.mpr h2n)
  refine ⟨D, hK, hiso, hpush, ?_, ?_, ?_⟩
  · rw [hΔ]
    change FrobeniusDiscrepancyBounds.candidate q n a ha
      (originalMultiStructureProjective k (q + 1) n a)
      (graphPrimeCurve q n a ha (originalMultiStructureProjective k (q + 1) n a)) = _
    rw [FrobeniusDiscrepancyBounds.candidate_graph]
    dsimp only
    field_simp
  · intro i
    rw [hΔ]
    change FrobeniusDiscrepancyBounds.candidate q n a ha
      (originalMultiStructureProjective k (q + 1) n a)
      (fiberPrimeCurve q n a ha (originalMultiStructureProjective k (q + 1) n a) i) = _
    rw [FrobeniusDiscrepancyBounds.candidate_fiber]
    dsimp only
    field_simp
  · intro i j
    rw [hΔ]
    exact FrobeniusDiscrepancyBounds.candidate_old_exceptional_eq_zero q n a ha
      (originalMultiStructureProjective k (q + 1) n a) i j

end Universal

/-! ### The proposition -/

section Existence

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Distinct centres in the algebraically closed (hence infinite) field. -/
private def centers (n : ℕ) : Fin n → k := fun i => Infinite.natEmbedding k i.val

private theorem centers_injective (n : ℕ) : Function.Injective (centers (k := k) n) := by
  intro i j hij
  exact Fin.val_injective ((Infinite.natEmbedding k).injective hij)

set_option maxHeartbeats 1000000 in
/-- **Proposition 10.1** (`prop:frobenius-family`, manuscript lines 2892–2933). For every prime
`p = q + 1`, every algebraically closed `k` of characteristic `p` and every `n ≥ 3`, the union's
Frobenius construction gives a contraction `π : S_{p,n} → X_{p,n}` (a minimal resolution) of a
normal klt surface with `ρ = 1` and `2n+1` singular points, an actual klt canonical Weil divisor
`K_X` (`ℚ`-Cartier), and:

* (D) the exceptional curves of `π` are exactly the `1 + n + nq` curves `retainedCurve`
  (`B, F_i, C_{ij}`), with intersection matrix `gram` (`B² = -p(n-2)`, `F_i² = -p`, `n` chains
  `A_{p-1}`) and disjoint blocks; `P_i` is exterior with `B·P_i = F_i·P_i = C_{i,p-1}·P_i = 1`
  and `P_i² = -1`;
* (M) `M = B + (n-2)b` (`contractingDivisor`) is nef and big, its null locus is exactly
  `D = ⋃ retainedCurve`, `M² = p(n-2)`, and the curves of `M`-degree zero are the curves of `D`;
* (L) `L = π^*(-K_X) ∼_ℚ t M` and `L · P_i = t`, `t = d/(p(n-2))`, `d = 2 - (p-2)(n-2)`;
* (λ) the discrepancy coefficients are `1 - 2/(p(n-2))` on `B`, `1 - 2/p` on `F_i`, `0` on `C_{ij}`;
* (sign) `X` is klt del Pezzo iff `-K_X` is `ℚ`-ample iff `p = 2 ∨ (p,n) = (3,3)`;
  `K_X ∼_ℚ 0` for `(p,n) = (3,4)`; `K_X` is `ℚ`-ample in all other cases;
* (L²) in the del Pezzo cases the resolution datum has `L² = d²/(p(n-2))`. -/
theorem frobeniusFamily (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)] (hn : 3 ≤ n) :
    ∃ (a : Fin n → k) (ha : Function.Injective a) (X : NormalProjectiveSurface k)
      (π : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ X.toScheme)
      (hmin : IsMinimalResolution
        (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) X π)
      (hproper : IsProper π) (hbir : IsBirationalScheme π) (hrank : X.picardRank = 1)
      (KX : X.WeilDivisor) (_ : IsCanonicalWeilDivisor X KX)
      (_ : IsKltWithCanonicalDivisor X KX) (hK : X.QCartier (rationalizeWeilDivisor X KX)),
      letI : IsProper π := hproper
      letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
      IsKlt X ∧ X.singularPoints.card = 2 * n + 1 ∧
      -- (D) the contracted curves
      (∀ C : (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
        IsExceptionalCurve π C ↔ ∃ l : RetainedLabel q n, C = retainedCurve q n a ha l) ∧
      Function.Injective (retainedCurve q n a ha) ∧
      Fintype.card (RetainedLabel q n) = 1 + n + n * q ∧
      (∀ l l' : RetainedLabel q n, (retainedCurve q n a ha l).intersectionNumber
        ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).primeCurveCartier
          (sourceRegular q n a ha) (retainedCurve q n a ha l')) = gram q n l l') ∧
      (∀ l l' : RetainedLabel q n, block l ≠ block l' →
        Disjoint (retainedCurve q n a ha l : Set (sourceSurface q n a ha
            (originalMultiStructureProjective k (q + 1) n a)).toScheme)
          (retainedCurve q n a ha l' : Set (sourceSurface q n a ha
            (originalMultiStructureProjective k (q + 1) n a)).toScheme)) ∧
      (∀ i : Fin n, ¬ IsExceptionalCurve π (newestCurveP q n a ha i)) ∧
      (∀ (l : RetainedLabel q n) (i : Fin n), (retainedCurve q n a ha l).intersectionNumber
        ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).primeCurveCartier
          (sourceRegular q n a ha) (newestCurveP q n a ha i)) = newestGram q n l i) ∧
      (∀ i i' : Fin n, (newestCurveP q n a ha i).intersectionNumber
        ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).primeCurveCartier
          (sourceRegular q n a ha) (newestCurveP q n a ha i')) = if i = i' then -1 else 0) ∧
      -- (M) the nef and big divisor `M = B + (n-2) b`
      Positivity.IsNef (multiStructure (q + 1) n a) (originalLine q n a ha) ∧
      Positivity.IsBig (multiStructure (q + 1) n a) (originalLine q n a ha) ∧
      Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha) =
        ⋃ l : RetainedLabel q n, (retainedCurve q n a ha l : Set (sourceSurface q n a ha
          (originalMultiStructureProjective k (q + 1) n a)).toScheme) ∧
      (∀ C : (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
        C.restrictionDegree (originalLine q n a ha) = 0 ↔
          ∃ l : RetainedLabel q n, C = retainedCurve q n a ha l) ∧
      (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).intersectionPairing
        (sourceRegular q n a ha)
        (contractingDivisor q n a ha (originalMultiStructureProjective k (q + 1) n a))
        (contractingDivisor q n a ha (originalMultiStructureProjective k (q + 1) n a)) =
        ((q + 1 : ℕ) : ℤ) * ((n : ℤ) - 2) ∧
      -- (L) `L = π^*(-K_X) ∼_ℚ t M` and `L · P_i = t`
      ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilClassMap
          (-QCartierPullback.pullback
            (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := X)
            π (rationalizeWeilDivisor X KX) hK) =
        ((2 - (((q + 1 : ℕ) : ℚ) - 2) * ((n : ℚ) - 2)) / (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2))) •
          (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilClassMap
            ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalCartierToWeilHom
              (contractingDivisor q n a ha (originalMultiStructureProjective k (q + 1) n a)))) ∧
      (∀ i : Fin n,
        (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalPicardRestrictionDegree
          (newestCurveP q n a ha i)
          ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilToRationalPicard
            (sourceRegular q n a ha)
            (-QCartierPullback.pullback
              (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := X)
              π (rationalizeWeilDivisor X KX) hK)) =
        (2 - (((q + 1 : ℕ) : ℚ) - 2) * ((n : ℚ) - 2)) / (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2))) ∧
      -- (λ) the discrepancy coefficients
      (∃ D : CartierDivisor (sourceSurface q n a ha
          (originalMultiStructureProjective k (q + 1) n a)).toScheme,
        Nonempty (cartierDivisorModule (sourceSurface q n a ha
            (originalMultiStructureProjective k (q + 1) n a)).toScheme D ≅
          relativeDifferentialExterior (multiStructure (q + 1) n a) 2) ∧
        BirationalWeilPushforward.pushforward
            (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (X := X)
            π hbir
            ((sourceSurface q n a ha
              (originalMultiStructureProjective k (q + 1) n a)).cartierToWeilHom D) = KX ∧
        ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalCartierToWeilHom D -
            QCartierPullback.pullback
              (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := X)
              π (rationalizeWeilDivisor X KX) hK)
            (retainedCurve q n a ha (.inl ())) =
          -(1 - 2 / (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2))) ∧
        (∀ i : Fin n,
          ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalCartierToWeilHom D -
            QCartierPullback.pullback
              (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := X)
              π (rationalizeWeilDivisor X KX) hK)
            (retainedCurve q n a ha (.inr (.inl i))) = -(1 - 2 / ((q + 1 : ℕ) : ℚ))) ∧
        (∀ (i : Fin n) (j : Fin q),
          ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalCartierToWeilHom D -
            QCartierPullback.pullback
              (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) (Y := X)
              π (rationalizeWeilDivisor X KX) hK)
            (retainedCurve q n a ha (.inr (.inr (i, j)))) = 0)) ∧
      -- (sign) the three canonical-sign cases
      (IsKltDelPezzo X ↔ q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3)) ∧
      (X.QAmple (-rationalizeWeilDivisor X KX) ↔ q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3)) ∧
      (((q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3)) ∧ X.QAmple (-rationalizeWeilDivisor X KX)) ∨
        ((q + 1 = 3 ∧ n = 4) ∧ X.QLinearlyEquivalent (rationalizeWeilDivisor X KX) 0) ∨
        ((q + 1 ≠ 2 ∧ (q + 1 ≠ 3 ∨ 5 ≤ n)) ∧ X.QAmple (rationalizeWeilDivisor X KX))) ∧
      -- (L²) in the del Pezzo cases
      (∀ hDP : IsKltDelPezzo X,
        (ResolutionDatum.mk (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
            X π hmin hDP hrank).Lsq =
          (2 - (((q + 1 : ℕ) : ℚ) - 2) * ((n : ℚ) - 2)) ^ 2 /
            (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2))) := by
  have hn2 : 2 < n := by omega
  let a : Fin n → k := centers n
  have ha : Function.Injective a := centers_injective n
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, X, π, hπ, hproper, hsurj, hbir, hc, hgeom,
      hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal,
      hKlt, hIsKlt, hsing, hcard, hcount⟩ :=
    exists_normal_projective_surface_rank_one_klt_exact_singular_count q n a ha hn2
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  have hKcanon : IsCanonicalWeilDivisor X
      (targetCanonicalWeil q n a ha hn2 X π hπ hbir hpoints hcriterion) :=
    targetCanonicalWeil_isCanonical q n a ha hn2 X π hπ hbir hpoints hcriterion
  have hK : X.QCartier (rationalizeWeilDivisor X
      (targetCanonicalWeil q n a ha hn2 X π hπ hbir hpoints hcriterion)) :=
    FrobeniusMultiCentreTargetQCartier.targetCanonicalWeil_qCartier
      q n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e
  obtain ⟨D, hK', hiso, hpush, hΔB, hΔF, hΔC⟩ :=
    discrepancy_coefficients q n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e
  refine ⟨a, ha, X, π, hminimal, hproper, hbir, hrank,
    targetCanonicalWeil q n a ha hn2 X π hπ hbir hpoints hcriterion, hKcanon, hKlt, hK, hIsKlt, hcard,
    isExceptionalCurve_iff_retained q n a ha hn2 X π hπ hcriterion,
    retainedCurve_injective q n a ha hn2,
    retainedLabel_card q n,
    retainedCurve_intersectionNumber q n a ha,
    retainedCurve_disjoint q n a ha,
    newestCurveP_not_exceptional q n a ha X π hπ hcriterion,
    retainedCurve_newest_intersectionNumber q n a ha,
    newestCurveP_intersectionNumber q n a ha,
    contractingLine_isNef q n a ha (originalMultiStructureProjective k (q + 1) n a) hn2.le,
    FrobeniusMultiCentreContractingBig.contractingLine_isBig q n a ha
      (originalMultiStructureProjective k (q + 1) n a) hn2,
    ?_,
    ?_,
    contractingDivisor_square q n a ha (originalMultiStructureProjective k (q + 1) n a),
    anticanonical_pullback_classMap q n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e hK,
    anticanonical_pullback_newest_degree q n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e hK,
    ⟨D, hiso, hpush, hΔB, hΔF, hΔC⟩,
    target_isKltDelPezzo_iff_parameters q n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e hA,
    targetCanonicalWeil_neg_qAmple_iff_parameters q n a ha hn2 X π hπ hbir hpoints hcriterion
      A m hm e hA,
    targetCanonicalWeil_parameter_sign_cases q n a ha hn2 X π hπ hbir hpoints hcriterion
      A m hm e hA,
    fun hDP => S01.lsq_frobenius_datum q n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e
      hminimal hDP hrank⟩
  · exact (FrobeniusMultiCentreContractingNullLocus.nullLocus_eq_support q n a ha
      (originalMultiStructureProjective k (q + 1) n a) hn2).trans
      (contractingSupport_eq_iUnion q n a ha)
  · intro C
    refine Iff.trans (FrobeniusMultiCentreNullCurveClassification.restrictionDegree_eq_zero_iff
      q n a ha (originalMultiStructureProjective k (q + 1) n a) hn2 C) ?_
    constructor
    · rintro (h | ⟨i, h⟩ | ⟨i, j, h⟩)
      · exact ⟨.inl (), h⟩
      · exact ⟨.inr (.inl i), h⟩
      · exact ⟨.inr (.inr (i, j)), h⟩
    · rintro ⟨l, rfl⟩
      rcases l with _ | (i | ⟨i, j⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨i, rfl⟩)
      · exact Or.inr (Or.inr ⟨i, j, rfl⟩)

end Existence

end KltDP.Manuscript.S10

#print axioms KltDP.Manuscript.S10.frobeniusFamily
