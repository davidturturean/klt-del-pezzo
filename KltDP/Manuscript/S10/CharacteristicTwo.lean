import KltDP.Manuscript.S01.Examples
import KltDP.Manuscript.Datum.AnticanonicalDegrees
import KltDP.Examples.FrobeniusCharacteristicTwoActualMinimum
import KltDP.Examples.FrobeniusCharacteristicTwoActualAdjoint
import KltDP.Examples.FrobeniusActualEvenHalfClass
import KltDP.Examples.FrobeniusMultiCentreNullCurveClassification
import KltDP.Examples.FrobeniusMultiCentreRulingFibers
import KltDP.Examples.FrobeniusActualStrictGraphInseparable
import KltDP.Geometry.SmoothCanonicalCartierRepresentative
import KltDP.Geometry.SmoothCanonicalExteriorComparison

/-!
# Theorem 10.2 (`thm:characteristic-two`, manuscript lines 3008–3085):
# rulings and divisibility on the Keel–McKernan family

The headline statements are `characteristicTwoFamily_code` (all `n ≥ 3`) and `sevenNodes_code`
(`n = 3`); the clauses are proved for an arbitrary contraction datum in the `Universal` section
and assembled from the union's existence theorem.
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
open KltDP.Examples.FrobeniusMultiCentreProjectiveSevenConfiguration
open KltDP.Examples.FrobeniusMultiCentreExceptionalPrime
open KltDP.Examples.FrobeniusMultiCentreSpecialNullCurves
open KltDP.Geometry.InvertibleSheafSectionPowers

universe u

namespace KltDP.Manuscript.S10

open KltDP.Manuscript

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

/-! ### Combinatorics of the doubled-even code `DE(n)` -/

/-- The number of even-cardinality subsets of an `n`-element set is `2^(n-1)`
(the code `DE(n)` has dimension `n - 1`). -/
theorem card_even_subsets (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun A : Finset (Fin n) => Even A.card)).card = 2 ^ (n - 1) := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let f : Finset (Fin n) → Finset (Fin n) :=
    fun A => if i0 ∈ A then A.erase i0 else insert i0 A
  have hf : ∀ A, f (f A) = A := by
    intro A
    by_cases h : i0 ∈ A
    · have h' : i0 ∉ A.erase i0 := Finset.not_mem_erase i0 A
      simp only [f, if_pos h, if_neg h', Finset.insert_erase h]
    · have h' : i0 ∈ insert i0 A := Finset.mem_insert_self i0 A
      simp only [f, if_neg h, if_pos h', Finset.erase_insert h]
  have hcard : ∀ A, Even (f A).card ↔ ¬ Even A.card := by
    intro A
    by_cases h : i0 ∈ A
    · have hpos : 1 ≤ A.card := Finset.card_pos.mpr ⟨i0, h⟩
      simp only [f, if_pos h, Finset.card_erase_of_mem h]
      rw [Nat.even_sub hpos]
      simp
    · simp only [f, if_neg h, Finset.card_insert_of_not_mem h]
      exact Nat.even_add_one
  have hbij : (Finset.univ.filter (fun A : Finset (Fin n) => Even A.card)).card =
      (Finset.univ.filter (fun A : Finset (Fin n) => ¬ Even A.card)).card := by
    refine Finset.card_bij' (fun A _ => f A) (fun A _ => f A) ?_ ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
      exact fun h => (hcard A).mp h hA
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
      exact (hcard A).mpr hA
    · intro A _
      exact hf A
    · intro A _
      exact hf A
  have htotal := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Finset (Fin n)))) (fun A : Finset (Fin n) => Even A.card)
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin, ← hbij] at htotal
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-- Nonzero words of `DE(n)` have weight at least four: a matched even selection `A = B`
with `A ≠ ∅` uses at least four nodes. -/
theorem code_min_weight {n : ℕ} (A B : Finset (Fin n)) (hAB : A = B) (hA : Even A.card)
    (hne : A ≠ ∅) : 4 ≤ A.card + B.card := by
  subst hAB
  have hpos : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  obtain ⟨m, hm⟩ := hA
  omega

/-! ### The surface `S_{2,n}` and its retained prime curves -/

section Universal

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

local instance projectiveLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

variable (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- The retained label `B` is the union's strict graph prime curve. -/
theorem primeCurve_graph :
    primeCurve n a ha (.inl ()) =
      graphPrimeCurve 1 n a ha (originalMultiStructureProjective k 2 n a) :=
  PrimeCurve.ext rfl

/-- The retained label `F_i` is the union's strict special fibre prime curve. -/
theorem primeCurve_fiber (i : Fin n) :
    primeCurve n a ha (.inr (.inl i)) =
      fiberPrimeCurve 1 n a ha (originalMultiStructureProjective k 2 n a) i :=
  PrimeCurve.ext rfl

/-- The retained label `U_i` is the union's old exceptional prime curve `C_{i1}`. -/
theorem primeCurve_node (i : Fin n) (j : Fin 1) :
    primeCurve n a ha (.inr (.inr i)) =
      exceptionalPrimeCurveSPn 1 n a ha i (.inl j) (originalMultiStructureProjective k 2 n a) := by
  obtain rfl : j = 0 := Subsingleton.elim j 0
  exact PrimeCurve.ext rfl

/-- The exterior curve `P_i = E_{i2}` (the newest exceptional curve of the `i`-th cluster). -/
abbrev newestCurve (i : Fin n) : (surface n a ha).PrimeCurve :=
  exceptionalPrimeCurveSPn 1 n a ha i (.inr PUnit.unit) (originalMultiStructureProjective k 2 n a)

/-- The intersection matrix of the `2n+1` retained curves: `B² = -(2n-4)`, `F_i² = U_i² = -2`,
and all distinct retained curves are orthogonal (the forest `[2n-4] + 2n A₁`). -/
theorem primeCurve_intersectionNumber (r s : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (primeCurve n a ha r).intersectionNumber (primeDivisor n a ha s) =
      if r = s then -FrobeniusCharacteristicTwo.retainedWeight n r else 0 :=
  FrobeniusMultiCentreRetainedPrimeCurves.retainedPrimeCurve_intersectionNumber n a ha
    (originalMultiStructureProjective k 2 n a) r s

theorem primeCurve_selfIntersectionNumber (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (primeCurve n a ha r).selfIntersectionNumber (surface_regularPoints n a ha) =
      -FrobeniusCharacteristicTwo.retainedWeight n r := by
  change (primeCurve n a ha r).intersectionNumber (primeDivisor n a ha r) = _
  rw [primeCurve_intersectionNumber, if_pos rfl]

theorem primeCurve_disjoint (r s : FrobeniusCharacteristicTwo.RetainedLabel n) (hrs : r ≠ s) :
    Disjoint (primeCurve n a ha r : Set (surface n a ha).toScheme)
      (primeCurve n a ha s : Set (surface n a ha).toScheme) := by
  simpa only [primeCurve_support] using
    FrobeniusMultiCentreRetainedCurves.retainedInclusion_disjoint n a ha r s hrs

/-- For `n ≥ 4` the graph `B` has square `4 - 2n < -2`, so it is not a node. -/
theorem graph_selfIntersectionNumber_lt (hn4 : 4 ≤ n) :
    (primeCurve n a ha (.inl ())).selfIntersectionNumber (surface_regularPoints n a ha) < -2 := by
  rw [primeCurve_selfIntersectionNumber]
  simp only [FrobeniusCharacteristicTwo.retainedWeight]
  omega

/-- Every `F_i` and every `U_i` is a `(-2)`-curve. -/
theorem node_selfIntersectionNumber (i : Fin n) :
    (primeCurve n a ha (.inr (.inl i))).selfIntersectionNumber (surface_regularPoints n a ha) = -2 ∧
    (primeCurve n a ha (.inr (.inr i))).selfIntersectionNumber (surface_regularPoints n a ha) = -2 := by
  constructor <;> rw [primeCurve_selfIntersectionNumber] <;> rfl

/-- The code of two-divisible subsets of the `2n` nodes `F_i, U_i`: an actual selection
`Σ_A F_i + Σ_B U_i` is twice a Picard class iff `A = B` and `|A|` is even (`DE(n)`). -/
theorem code_even_iff (A B : Finset (Fin n)) :
    (∃ c : Additive (surface n a ha).toScheme.Pic,
      (2 : ℤ) • c = cartierPicardHom (surface n a ha).toScheme
        ((∑ i ∈ A, primeDivisor n a ha (.inr (.inl i))) +
          ∑ i ∈ B, primeDivisor n a ha (.inr (.inr i)))) ↔
      A = B ∧ Even A.card :=
  FrobeniusMultiCentrePrimeEvenSelections.selectedPrimeNodeDivisor_even_iff n a ha
    (originalMultiStructureProjective k 2 n a) A B

/-- The half-class of the even word `Σ_{i∈A}(F_i + U_i)` is `(|A|/2) b - Σ_{i∈A} P_i`. -/
theorem code_half_class (A : Finset (Fin n)) (hA : Even A.card) :
    (2 : ℤ) • (((A.card / 2 : ℕ) : ℤ) • multiSecondFiberClass 2 n a -
      ∑ i ∈ A, exceptionalClass 2 n a i (1 : Fin 2)) =
      cartierPicardHom (surface n a ha).toScheme
        ((∑ i ∈ A, primeDivisor n a ha (.inr (.inl i))) +
          ∑ i ∈ A, primeDivisor n a ha (.inr (.inr i))) :=
  FrobeniusActualEvenHalfClass.selected_prime_divisor_explicit_half n a ha A hA

/-! ### Exceptional curves of the contraction -/

variable (hn : 2 < n) (Y : NormalProjectiveSurface k)
    (π : (surface n a ha).toScheme ⟶ Y.toScheme)
    (hπ : π ≫ Y.structureMorphism = multiStructure 2 n a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (surface n a ha).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine 1 n a ha) = 0)

include hn hπ hcriterion in
/-- The exceptional curves of the contraction are exactly the `2n+1` retained prime curves. -/
theorem isExceptionalCurve_iff (C : (surface n a ha).PrimeCurve) :
    IsExceptionalCurve π C ↔
      ∃ r : FrobeniusCharacteristicTwo.RetainedLabel n, C = primeCurve n a ha r := by
  constructor
  · intro hC
    have hzero : C.restrictionDegree (originalLine 1 n a ha) = 0 :=
      (hcriterion C).mp (IsExceptionalCurve.exists_fieldPoint_factor π hπ C hC)
    rcases (FrobeniusMultiCentreNullCurveClassification.restrictionDegree_eq_zero_iff 1 n a ha
        (originalMultiStructureProjective k 2 n a) hn C).mp hzero with h | ⟨i, h⟩ | ⟨i, j, h⟩
    · exact ⟨.inl (), h.trans (primeCurve_graph n a ha).symm⟩
    · exact ⟨.inr (.inl i), h.trans (primeCurve_fiber n a ha i).symm⟩
    · exact ⟨.inr (.inr i), h.trans (primeCurve_node n a ha i j).symm⟩
  · rintro ⟨r, rfl⟩
    have hzero : (primeCurve n a ha r).restrictionDegree (originalLine 1 n a ha) = 0 := by
      apply (FrobeniusMultiCentreNullCurveClassification.restrictionDegree_eq_zero_iff 1 n a ha
        (originalMultiStructureProjective k 2 n a) hn _).mpr
      rcases r with _ | (i | i)
      · exact Or.inl (primeCurve_graph n a ha)
      · exact Or.inr (Or.inl ⟨i, primeCurve_fiber n a ha i⟩)
      · exact Or.inr (Or.inr ⟨i, 0, primeCurve_node n a ha i 0⟩)
    obtain ⟨p, hp, -⟩ := (hcriterion _).mpr hzero
    exact IsExceptionalCurve.of_fieldPoint_factor π _ p hp

/-! ### The resolution datum of the contraction and its anticanonical pullback -/

variable [IsProper π] [Surjective π] [IsIso π.c]
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine 1 n a ha) m).obj)
    (hmin : IsMinimalResolution (surface n a ha) Y π) (hDP : IsKltDelPezzo Y)
    (hrank : Y.picardRank = 1)

/-- The resolution datum `(S_{2,n}, X_{2,n}, π)` of the contraction. -/
abbrev datum : ResolutionDatum k := ⟨surface n a ha, Y, π, hmin, hDP, hrank⟩

include hπ hcriterion in
/-- `P_i` is exterior (not contracted). -/
theorem newestCurve_not_exceptional (i : Fin n) : ¬ IsExceptionalCurve π (newestCurve n a ha i) :=
  FrobeniusCharacteristicTwoGeometry.newest_not_exceptional (n := n) (a := a) (ha := ha)
    (Y := Y) (π := π) (hπ := hπ) (hcriterion := hcriterion) i


include hn hπ hbir hconnected hcriterion hm e in
/-- `L = π^*(-K_X) ∼_ℚ M/(n-2)` with `M` the union's contracting divisor `B + (n-2) b`. -/
theorem datum_Lweil_classMap :
    (surface n a ha).rationalWeilClassMap (datum n a ha Y π hmin hDP hrank).Lweil =
      (1 / ((n : ℚ) - 2)) • (surface n a ha).rationalWeilClassMap
        ((surface n a ha).rationalCartierToWeilHom
          (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a))) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  set R : ResolutionDatum k := datum n a ha Y π hmin hDP hrank with hR
  let K0 : Y.WeilDivisor := targetCanonicalWeil 1 n a ha hn Y π hπ hbir hconnected hcriterion
  have hK0canon : IsCanonicalWeilDivisor Y K0 :=
    targetCanonicalWeil_isCanonical 1 n a ha hn Y π hπ hbir hconnected hcriterion
  have hK0qc : Y.QCartier (rationalizeWeilDivisor Y K0) :=
    FrobeniusMultiCentreTargetQCartier.targetCanonicalWeil_qCartier
      1 n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  have hlin : Y.LinearlyEquivalent R.KX K0 :=
    IsCanonicalWeilDivisor.linearlyEquivalent R.KX_klt.1 hK0canon
  have hclass1 : (surface n a ha).rationalWeilClassMap R.pullbackKX =
      (surface n a ha).rationalWeilClassMap
        (QCartierPullback.pullback (X := surface n a ha) (Y := Y) π
          (rationalizeWeilDivisor Y K0) hK0qc) :=
    ((surface n a ha).rationalWeilClassMap_eq_iff _ _).mpr
      (QCartierPullback.pullback_qLinearlyEquivalent (X := surface n a ha) (Y := Y) π _ _
        R.KX_qCartier hK0qc (Y.qLinearlyEquivalent_of_linearlyEquivalent hlin))
  have hanti : (surface n a ha).rationalWeilClassMap
      (-QCartierPullback.pullback (X := surface n a ha) (Y := Y) π
        (rationalizeWeilDivisor Y K0) hK0qc) =
      (1 / ((n : ℚ) - 2)) • (surface n a ha).rationalWeilClassMap
        ((surface n a ha).rationalCartierToWeilHom
          (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a))) :=
    FrobeniusCharacteristicTwoGeometry.anticanonicalPullback_class
      n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  rw [map_neg] at hanti
  change (surface n a ha).rationalWeilClassMap (-R.pullbackKX) = _
  rw [map_neg, hclass1]
  exact hanti

include hn hπ hbir hconnected hcriterion hm e in
/-- `L · C = (1/(n-2)) (M · C)` for every prime curve `C`. -/
theorem datum_Ldeg_eq (C : (surface n a ha).PrimeCurve) :
    (datum n a ha Y π hmin hDP hrank).Ldeg C =
      (1 / ((n : ℚ) - 2)) * (C.intersectionNumber
        (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a)) : ℚ) := by
  set R : ResolutionDatum k := datum n a ha Y π hmin hDP hrank with hR
  have hclass := datum_Lweil_classMap n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
    hmin hDP hrank
  have hnum : R.S.rationalWeilNumericalMap R.hreg R.Lweil =
      (1 / ((n : ℚ) - 2)) • R.S.rationalWeilNumericalMap R.hreg
        (R.S.rationalCartierToWeilHom
          (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a))) := by
    rw [← R.S.rationalWeilClassNumericalMap_class R.hreg,
      ← R.S.rationalWeilClassNumericalMap_class R.hreg, ← map_smul]
    exact congrArg _ hclass
  change RationalWeilIntersection.degreeLinearMap R.S R.hreg C R.Lweil = _
  rw [← R.numericalRestrictionDegree_rationalWeilNumericalMap C R.Lweil, hnum, map_smul,
    smul_eq_mul, R.numericalRestrictionDegree_rationalWeilNumericalMap,
    RationalWeilIntersection.degreeLinearMap_rationalCartier]

include hn hπ hbir hconnected hcriterion hm e in
/-- The datum's `L`-degree is the union's `anticanonicalDegree`. -/
theorem datum_Ldeg_eq_anticanonicalDegree (C : (surface n a ha).PrimeCurve) :
    (datum n a ha Y π hmin hDP hrank).Ldeg C =
      FrobeniusCharacteristicTwoGeometry.anticanonicalDegree n a ha hn Y π hπ hbir hconnected
        hcriterion A m hm e C := by
  rw [datum_Ldeg_eq n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hmin hDP hrank C,
    FrobeniusCharacteristicTwoGeometry.anticanonicalDegree_eq]
  rfl

include hn hπ hbir hconnected hcriterion hm e in
/-- `ℓ_ext = 1/(n-2)`: the least `L`-degree of an exterior prime curve is `1/(n-2)`, attained. -/
theorem datum_Ldeg_isLeast :
    IsLeast {d : ℚ | ∃ C : (surface n a ha).PrimeCurve,
      ¬ IsExceptionalCurve π C ∧ d = (datum n a ha Y π hmin hDP hrank).Ldeg C}
      (1 / ((n : ℚ) - 2)) := by
  have h := FrobeniusCharacteristicTwoGeometry.anticanonicalDegree_isLeast_exterior
    n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  have hset : {d : ℚ | ∃ C : (surface n a ha).PrimeCurve,
      ¬ IsExceptionalCurve π C ∧ d = (datum n a ha Y π hmin hDP hrank).Ldeg C} =
      {d : ℚ | ∃ C : (surface n a ha).PrimeCurve, ¬ IsExceptionalCurve π C ∧
        d = FrobeniusCharacteristicTwoGeometry.anticanonicalDegree n a ha hn Y π hπ hbir
          hconnected hcriterion A m hm e C} := by
    ext d
    simp only [Set.mem_setOf_eq,
      datum_Ldeg_eq_anticanonicalDegree n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
        hmin hDP hrank]
  rw [hset]
  exact h

include hn hπ hbir hconnected hcriterion hm e in
/-- `L · P_i = 1/(n-2)`. -/
theorem datum_Ldeg_newestCurve (i : Fin n) :
    (datum n a ha Y π hmin hDP hrank).Ldeg (newestCurve n a ha i) = 1 / ((n : ℚ) - 2) := by
  rw [datum_Ldeg_eq_anticanonicalDegree n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
    hmin hDP hrank]
  exact FrobeniusCharacteristicTwoGeometry.newest_anticanonicalDegree
    n a ha hn Y π hπ hbir hconnected hcriterion A m hm e i

include hn hπ hbir hconnected hcriterion hm e in
/-- The class of `L` in `Pic(S)_ℚ` is `(1/(n-2))` times the realization of the integral vector
`nefVector 2 n = (2, n-1, -1, …, -1) = 2a + (n-1)b - Σ_i (E_{i1} + E_{i2})`. -/
theorem datum_Lweil_rationalPicard :
    (surface n a ha).rationalWeilToRationalPicard (surface_regularPoints n a ha)
        (datum n a ha Y π hmin hDP hrank).Lweil =
      (1 / ((n : ℚ) - 2)) • (surface n a ha).picardTensorInclusion
        (FrobeniusMultiCentrePicardRealization.realization 1 n a
          (FrobeniusPicard.nefVector 2 n)) := by
  have h := (surface n a ha).rationalWeilToRationalPicard_of_class_eq_smul_cartier
    (surface_regularPoints n a ha) _
    (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a)) _
    (datum_Lweil_classMap n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hmin hDP hrank)
  have hc : cartierPicardHom (surface n a ha).toScheme
      (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a)) =
      contractingClass 1 n a ha :=
    contractingDivisor_class 1 n a ha (originalMultiStructureProjective k 2 n a)
  rw [hc, contractingClass_eq_realization] at h
  exact h

/-- The manuscript's coordinates of `(n-2) L`: `nefVector 2 n = (2, n-1, -1,…,-1)`. -/
theorem nefVector_two_coordinates :
    FrobeniusPicard.nefVector 2 n = ((2 : ℤ), (n : ℤ) - 1, fun _ => (-1 : ℤ)) := rfl

omit [CharP k 2] [IsProper π] [Surjective π] [IsIso π.c] in
/-- The chosen canonical divisor `K_S` of the datum and the union's `canonicalCartier` have the
same rational class (both are Cartier representatives of the canonical sheaf). -/
theorem datum_KS_classMap :
    (surface n a ha).rationalWeilClassMap
        ((surface n a ha).rationalCartierToWeilHom (datum n a ha Y π hmin hDP hrank).KS) =
      (surface n a ha).rationalWeilClassMap
        ((surface n a ha).rationalCartierToWeilHom
          (canonicalCartier 1 n a ha (originalMultiStructureProjective k 2 n a))) := by
  set R : ResolutionDatum k := datum n a ha Y π hmin hDP hrank with hR
  letI : IsSmoothOfRelativeDimension 2 (surface n a ha).structureMorphism :=
    multiStructure_smoothTwo 2 n a ha
  have eD : cartierDivisorModule (surface n a ha).toScheme R.KS ≅
      (SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface
        (surface n a ha).structureMorphism).obj :=
    R.eKS ≪≫ (SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior
      (surface n a ha).structureMorphism).symm
  have eE : cartierDivisorModule (surface n a ha).toScheme
      (canonicalCartier 1 n a ha (originalMultiStructureProjective k 2 n a)) ≅
      (SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface
        (surface n a ha).structureMorphism).obj :=
    canonicalCartierIso 1 n a ha (originalMultiStructureProjective k 2 n a)
  have hlin := SmoothCanonicalCartierRepresentative.choices_linearlyEquivalent (surface n a ha)
    R.KS (canonicalCartier 1 n a ha (originalMultiStructureProjective k 2 n a)) eD eE
  exact ((surface n a ha).rationalWeilClassMap_eq_iff _ _).mpr
    ((surface n a ha).qLinearlyEquivalent_of_linearlyEquivalent hlin)

include hn hπ hbir hconnected hcriterion hm e in
/-- The adjoint identity `L + ℓ_ext K_S = ((n-3)/(n-2)) b` in `Pic(S)_ℚ`. -/
theorem datum_adjoint :
    (surface n a ha).rationalWeilToRationalPicard (surface_regularPoints n a ha)
        ((datum n a ha Y π hmin hDP hrank).Lweil +
          (1 / ((n : ℚ) - 2)) • (surface n a ha).rationalCartierToWeilHom
            (datum n a ha Y π hmin hDP hrank).KS) =
      (((n : ℚ) - 3) / ((n : ℚ) - 2)) •
        (surface n a ha).picardTensorInclusion (multiSecondFiberClass 2 n a) := by
  have hadj := FrobeniusCharacteristicTwoGeometry.anticanonicalPullback_adjoint
    n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  have hL : (surface n a ha).rationalWeilToRationalPicard (surface_regularPoints n a ha)
      (datum n a ha Y π hmin hDP hrank).Lweil =
      (surface n a ha).rationalWeilToRationalPicard (surface_regularPoints n a ha)
        (FrobeniusCharacteristicTwoGeometry.anticanonicalPullback n a ha hn Y π hπ hbir
          hconnected hcriterion A m hm e) := by
    have hac : (surface n a ha).rationalWeilClassMap
        (FrobeniusCharacteristicTwoGeometry.anticanonicalPullback n a ha hn Y π hπ hbir
          hconnected hcriterion A m hm e) =
        (1 / ((n : ℚ) - 2)) • (surface n a ha).rationalWeilClassMap
          ((surface n a ha).rationalCartierToWeilHom
            (contractingDivisor 1 n a ha (originalMultiStructureProjective k 2 n a))) :=
      FrobeniusCharacteristicTwoGeometry.anticanonicalPullback_class
        n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
    rw [(surface n a ha).rationalWeilToRationalPicard_apply,
      (surface n a ha).rationalWeilToRationalPicard_apply,
      datum_Lweil_classMap n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hmin hDP hrank,
      hac]
  have hK : (surface n a ha).rationalWeilToRationalPicard (surface_regularPoints n a ha)
      ((surface n a ha).rationalCartierToWeilHom (datum n a ha Y π hmin hDP hrank).KS) =
      (surface n a ha).rationalWeilToRationalPicard (surface_regularPoints n a ha)
        ((surface n a ha).rationalCartierToWeilHom
          (canonicalCartier 1 n a ha (originalMultiStructureProjective k 2 n a))) := by
    rw [(surface n a ha).rationalWeilToRationalPicard_apply,
      (surface n a ha).rationalWeilToRationalPicard_apply,
      datum_KS_classMap n a ha Y π hmin hDP hrank]
  rw [map_add, map_smul, hL, hK, ← map_smul, ← map_add]
  exact hadj

include hn hπ hbir hconnected hcriterion hm e in
/-- `K_{X_{2,n}}² = L² = 2/(n-2)`. -/
theorem datum_Lsq : (datum n a ha Y π hmin hDP hrank).Lsq = 2 / ((n : ℚ) - 2) := by
  have h := S01.lsq_frobenius_datum 1 n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
    hmin hDP hrank
  have hr0 : ((n : ℚ) - 2) ≠ 0 := by
    have h2n : (2 : ℚ) < n := by exact_mod_cast hn
    exact ne_of_gt (sub_pos.mpr h2n)
  refine h.trans ?_
  push_cast
  field_simp
  ring

/-! ### The ruling of class `b`: special fibres `F_i + U_i + 2 P_i`, irreducible other fibres -/

omit [IsProper π] [Surjective π] [IsIso π.c] in
/-- The class of `P_i` is the negative of the class of the kernel line of `E_{i2}`. -/
theorem newestCurve_cartierClass (i : Fin n) :
    cartierPicardHom (surface n a ha).toScheme
      ((surface n a ha).primeCurveCartier (surface_regularPoints n a ha) (newestCurve n a ha i)) =
      -Additive.ofMul (FrobeniusMultiCentreExceptionalGlobalClasses.exceptionalKernelLine
        1 n a ha i (.inr PUnit.unit)).toPic := by
  letI := exceptionalCurve_isIntegral 1 n a ha i (.inr PUnit.unit)
  exact PrimeCurveTransversalPoint.cartierPicardHom_primeCurveCartier_of_kernel
    (surface_regularPoints n a ha) (newestCurve n a ha i)
    (FrobeniusMultiCentreExceptional.exceptionalCurveι 1 n a i (.inr PUnit.unit)) rfl
    (FrobeniusMultiCentreExceptionalGlobalClasses.exceptionalKernelLine 1 n a ha i (.inr PUnit.unit))
    rfl

omit [IsProper π] [Surjective π] [IsIso π.c] in
/-- The special scheme-theoretic fibre of the ruling of class `b` over the `i`-th selected height:
`b = F_i + U_i + 2 P_i` in `Pic(S)`. -/
theorem secondFiberClass_eq (i : Fin n) :
    multiSecondFiberClass 2 n a =
      cartierPicardHom (surface n a ha).toScheme (primeDivisor n a ha (.inr (.inl i))) +
        cartierPicardHom (surface n a ha).toScheme (primeDivisor n a ha (.inr (.inr i))) +
        (2 : ℤ) • cartierPicardHom (surface n a ha).toScheme
          ((surface n a ha).primeCurveCartier (surface_regularPoints n a ha)
            (newestCurve n a ha i)) := by
  rw [primeDivisor_class, primeDivisor_class, newestCurve_cartierClass]
  have h := FrobeniusMultiCentreExceptionalChainNumerics.secondFiber_eq_fiberKernel_add_weighted_chain
    1 n a ha i
  have h0 : FrobeniusMultiCentreExceptionalChainNumerics.chainKernelClass 1 n a ha i 0 =
      -Additive.ofMul (FrobeniusMultiCentreExceptionalGlobalClasses.exceptionalKernelLine
        1 n a ha i (.inl (0 : Fin 1))).toPic :=
    FrobeniusMultiCentreExceptionalChainNumerics.chainKernelClass_castSucc 1 n a ha i 0
  have h1 : FrobeniusMultiCentreExceptionalChainNumerics.chainKernelClass 1 n a ha i 1 =
      -Additive.ofMul (FrobeniusMultiCentreExceptionalGlobalClasses.exceptionalKernelLine
        1 n a ha i (.inr PUnit.unit)).toPic :=
    FrobeniusMultiCentreExceptionalChainNumerics.chainKernelClass_last 1 n a ha i
  have hsum : (∑ j : Fin (1 + 1), (j.val + 1) •
      FrobeniusMultiCentreExceptionalChainNumerics.chainKernelClass 1 n a ha i j) =
      (1 : ℕ) • FrobeniusMultiCentreExceptionalChainNumerics.chainKernelClass 1 n a ha i 0 +
        (2 : ℕ) • FrobeniusMultiCentreExceptionalChainNumerics.chainKernelClass 1 n a ha i 1 :=
    Fin.sum_univ_two _
  rw [hsum, h0, h1] at h
  change multiSecondFiberClass (1 + 1) n a = _
  rw [h, one_nsmul, add_assoc]
  rfl

omit [IsProper π] [Surjective π] [IsIso π.c] in
/-- The support of the fibre of the ruling over the `i`-th selected height `y = a_i²` is
`F_i ∪ U_i ∪ P_i`. -/
theorem secondRuling_special_fiber_eq (i : Fin n) :
    (multiProjection 2 n a ≫ FrobeniusGraphClosed.secondProjection).base ⁻¹'
        {FrobeniusProjectivePoints.point (a i ^ 2)} =
      (primeCurve n a ha (.inr (.inl i)) : Set (surface n a ha).toScheme) ∪
        (primeCurve n a ha (.inr (.inr i)) : Set (surface n a ha).toScheme) ∪
        (newestCurve n a ha i : Set (surface n a ha).toScheme) := by
  have h := FrobeniusMultiCentreRulingFibers.secondRuling_special_preimage 1 n a ha i
  have hU : (⋃ idx : FrobeniusExceptionalFinalConfiguration.FinalIndex.{0} 1,
      FrobeniusMultiCentreExceptional.exceptionalSupport 1 n a i idx) =
      FrobeniusMultiCentreExceptional.exceptionalSupport 1 n a i (.inl (0 : Fin 1)) ∪
        FrobeniusMultiCentreExceptional.exceptionalSupport 1 n a i (.inr PUnit.unit) := by
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun idx => ?_
      rcases idx with j | u
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        exact Set.subset_union_left
      · exact Set.subset_union_right
    · exact Set.union_subset (Set.subset_iUnion _ (Sum.inl (0 : Fin 1)))
        (Set.subset_iUnion _ (Sum.inr PUnit.unit))
  refine h.trans ?_
  rw [hU, ← Set.union_assoc]
  rfl

omit [CharP k 2] [IsProper π] [Surjective π] [IsIso π.c] in
/-- Every other fibre of the ruling (over a closed point that is not a selected height) is
irreducible: it is the image of a projective line. -/
theorem secondRuling_fiber_irreducible (z : projectiveSpace k 1)
    (hz : IsClosed ({z} : Set (projectiveSpace k 1)))
    (hsel : ∀ i : Fin n, z ≠ FrobeniusProjectivePoints.point (a i ^ 2)) :
    IsIrreducible ((multiProjection 2 n a ≫ FrobeniusGraphClosed.secondProjection).base ⁻¹' {z}) := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  rcases ProjectiveLineClosedPoints.eq_point_or_eq_infinity z hz with ⟨c, rfl⟩ | rfl
  · have hc : ∀ j : Fin n, c ≠ a j ^ (1 + 1) := fun j hj => hsel j (by rw [hj])
    have hr : Set.range (FrobeniusSpecialFiberSPn.unaffectedFiberLift 1 n a c hc).base =
        (multiProjection 2 n a ≫ FrobeniusGraphClosed.secondProjection).base ⁻¹'
          {FrobeniusProjectivePoints.point c} :=
      FrobeniusNonspecialRulingPrimeCurve.range_unaffectedFiberLift 1 n a c hc
    rw [← hr, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (projectiveSpace k 1)).image _
      (FrobeniusSpecialFiberSPn.unaffectedFiberLift 1 n a c hc).continuous.continuousOn
  · have hr : Set.range (FrobeniusInfinityRulingPrimeCurve.infinityFiberLift 1 n a).base =
        (multiProjection 2 n a ≫ FrobeniusGraphClosed.secondProjection).base ⁻¹'
          {ProjectiveLinePointAtInfinity.infinityPoint} :=
      FrobeniusInfinityRulingPrimeCurve.range_infinityFiberLift 1 n a
    rw [← hr, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (projectiveSpace k 1)).image _
      (FrobeniusInfinityRulingPrimeCurve.infinityFiberLift 1 n a).continuous.continuousOn

omit [IsProper π] [Surjective π] [IsIso π.c] in
/-- `B` is the strict graph; the ruling of class `b` restricted to `B` has function-field degree
two and is purely inseparable (`B` is a purely inseparable bisection). -/
theorem graph_inseparable_bisection :
    (primeCurve n a ha (.inl ()) : Set (surface n a ha).toScheme) =
      Set.range (FrobeniusMultiCentreGraphFiber.graphStrictι 2 n a).base ∧
    (letI : Algebra (projectiveSpace k 1).functionField
        (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField :=
      (functionFieldMap (FrobeniusActualStrictGraphInseparable.strictGraphRuling n a)).hom.toAlgebra
     letI : Module (projectiveSpace k 1).functionField
        (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField := Algebra.toModule
     Module.finrank (projectiveSpace k 1).functionField
      (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField = 2) ∧
    (letI : Algebra (projectiveSpace k 1).functionField
        (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField :=
      (functionFieldMap (FrobeniusActualStrictGraphInseparable.strictGraphRuling n a)).hom.toAlgebra
     IsPurelyInseparable (projectiveSpace k 1).functionField
      (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField) :=
  ⟨rfl, FrobeniusActualStrictGraphInseparable.strictGraphRuling_finrank n a,
    FrobeniusActualStrictGraphInseparable.strictGraphRuling_isPurelyInseparable n a⟩

end Universal

/-! ### `n = 3`: the seven isolated nodes -/

section Seven

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable (a : Fin 3 → k) (ha : Function.Injective a)

/-- **Theorem 10.2, `n = 3`**: all seven retained curves are isolated `(-2)`-nodes (seven disjoint
smooth rational curves of square `-2`), the two-divisible selections of the seven nodes are
exactly the eight binary selections satisfying the parity conditions (a code of dimension three:
`2^3 = 8` words), the seven nonzero words have weight four, and each word has the explicit
half-class `halfClass`. -/
theorem sevenNodes_code :
    (Fintype.card (FrobeniusCharacteristicTwo.RetainedLabel 3) = 7 ∧
      Function.Injective (primeCurve 3 a ha) ∧
      (∀ r s : FrobeniusCharacteristicTwo.RetainedLabel 3, r ≠ s →
        Disjoint (primeCurve 3 a ha r : Set (surface 3 a ha).toScheme)
          (primeCurve 3 a ha s : Set (surface 3 a ha).toScheme)) ∧
      (∀ r : FrobeniusCharacteristicTwo.RetainedLabel 3,
        IsSmooth (primeCurve 3 a ha r).toSpec ∧
        (∃ e : (primeCurve 3 a ha r).toScheme ≅ projectiveSpace k 1,
          e.hom ≫ projectiveSpaceToSpec k 1 = (primeCurve 3 a ha r).toSpec) ∧
        (primeCurve 3 a ha r).selfIntersectionNumber (surface_regularPoints 3 a ha) = -2)) ∧
    (∀ s : FrobeniusSevenNodes.Selection,
      (∃ c : Additive (surface 3 a ha).toScheme.Pic,
        (2 : ℤ) • c = cartierPicardHom (surface 3 a ha).toScheme (sevenDivisor a ha s)) ↔
        FrobeniusSevenNodes.parityConditions s) ∧
    (FrobeniusMultiCentrePrimeEvenSelections.evenPrimeSelections a ha
      (originalMultiStructureProjective k 2 3 a)).card = 2 ^ 3 ∧
    ((FrobeniusMultiCentrePrimeEvenSelections.evenPrimeSelections a ha
      (originalMultiStructureProjective k 2 3 a)).erase FrobeniusSevenNodes.emptySelection).card = 7 ∧
    (∀ s ∈ FrobeniusMultiCentrePrimeEvenSelections.evenPrimeSelections a ha
        (originalMultiStructureProjective k 2 3 a),
      s ≠ FrobeniusSevenNodes.emptySelection → FrobeniusSevenNodes.selectionWeight s = 4) ∧
    (∀ s : FrobeniusSevenNodes.Selection, FrobeniusSevenNodes.parityConditions s →
      (2 : ℤ) • halfClass a ha s = cartierPicardHom (surface 3 a ha).toScheme (sevenDivisor a ha s)) :=
  ⟨sevenCurve_configuration a ha, sevenDivisor_even_iff a ha,
    FrobeniusMultiCentrePrimeEvenSelections.evenPrimeSelections_card a ha _,
    FrobeniusMultiCentrePrimeEvenSelections.nonempty_evenPrimeSelections_card a ha _,
    fun s hs hne => FrobeniusMultiCentrePrimeEvenSelections.nonempty_evenPrimeSelection_weight
      a ha _ s hs hne,
    fun s hs => two_smul_halfClass a ha s hs⟩

end Seven

/-! ### The theorem -/

section Existence

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

local instance primeTwoE : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

local instance projectiveLineIntegralE : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- Distinct centres in the algebraically closed (hence infinite) field. -/
private def centers (n : ℕ) : Fin n → k := fun i => Infinite.natEmbedding k i.val

omit [CharP k 2] in
private theorem centers_injective (n : ℕ) : Function.Injective (centers (k := k) n) := by
  intro i j hij
  exact Fin.val_injective ((Infinite.natEmbedding k).injective hij)

/-- **Theorem 10.2** (`thm:characteristic-two`, manuscript lines 3008–3045). Over an algebraically
closed field of characteristic two and for `n ≥ 3`, the Frobenius construction `S_{2,n} → X_{2,n}`
(the union's `surface n a ha` with the contraction `π`, datum `datum`) gives:

1. a rank-one klt del Pezzo surface `X_{2,n}` with `2n+1` singular points and
   `K_{X_{2,n}}² = L² = 2/(n-2)`;
2. the exceptional curves of `π` are exactly the `2n+1` retained curves `B, F_i, U_i`
   (`primeCurve`), pairwise disjoint, with `B² = -(2n-4)` and `F_i² = U_i² = -2`
   (the forest `[2n-4] + 2n A₁`);
3. `L = (2a + (n-1)b - Σ_i(E_{i1}+E_{i2}))/(n-2)` (the class of `L` is `1/(n-2)` times the
   realization of `nefVector 2 n = (2, n-1, -1, …, -1)`), `ℓ_ext = 1/(n-2)` is the least exterior
   degree and is attained by every exterior curve `P_i`, and `L + ℓ_ext K_S = ((n-3)/(n-2)) b`;
4. the ruling of class `b` has the `n` special fibres `F_i + U_i + 2P_i` (as classes and as
   supports over the selected heights) and every other fibre is irreducible;
5. `B` is the strict graph and the ruling restricted to `B` has function-field degree two and is
   purely inseparable (a purely inseparable bisection);
6. for `n ≥ 4`, `B² < -2`; the two-divisible selections of the `2n` nodes `F_i, U_i` are exactly
   the matched even selections `Σ_{i∈A}(F_i+U_i)` with `|A|` even (the code `DE(n)`), with
   half-class `(|A|/2) b - Σ_{i∈A} P_i`; there are `2^(n-1)` words (dimension `n-1`) and every
   nonzero word has weight `≥ 4`. -/
theorem characteristicTwoFamily_code (n : ℕ) (hn : 3 ≤ n) :
    ∃ (a : Fin n → k) (ha : Function.Injective a) (X : NormalProjectiveSurface k)
      (π : (surface n a ha).toScheme ⟶ X.toScheme)
      (hmin : IsMinimalResolution (surface n a ha) X π) (hDP : IsKltDelPezzo X)
      (hrank : X.picardRank = 1),
      -- (1) singular points and the anticanonical square
      X.singularPoints.card = 2 * n + 1 ∧
      (datum n a ha X π hmin hDP hrank).Lsq = 2 / ((n : ℚ) - 2) ∧
      -- (2) the exceptional forest `[2n-4] + 2n A₁`
      (∀ C : (surface n a ha).PrimeCurve, IsExceptionalCurve π C ↔
        ∃ r : FrobeniusCharacteristicTwo.RetainedLabel n, C = primeCurve n a ha r) ∧
      Function.Injective (primeCurve n a ha) ∧
      Fintype.card (FrobeniusCharacteristicTwo.RetainedLabel n) = 2 * n + 1 ∧
      (∀ r s : FrobeniusCharacteristicTwo.RetainedLabel n, r ≠ s →
        Disjoint (primeCurve n a ha r : Set (surface n a ha).toScheme)
          (primeCurve n a ha s : Set (surface n a ha).toScheme)) ∧
      (∀ r s : FrobeniusCharacteristicTwo.RetainedLabel n,
        (primeCurve n a ha r).intersectionNumber (primeDivisor n a ha s) =
          if r = s then -FrobeniusCharacteristicTwo.retainedWeight n r else 0) ∧
      (primeCurve n a ha (.inl ())).selfIntersectionNumber (surface_regularPoints n a ha) =
        -(2 * ((n : ℤ) - 2)) ∧
      (∀ i : Fin n,
        (primeCurve n a ha (.inr (.inl i))).selfIntersectionNumber
          (surface_regularPoints n a ha) = -2 ∧
        (primeCurve n a ha (.inr (.inr i))).selfIntersectionNumber
          (surface_regularPoints n a ha) = -2) ∧
      -- (3) `L`, `ℓ_ext`, the adjoint
      ((surface n a ha).rationalWeilToRationalPicard (surface_regularPoints n a ha)
          (datum n a ha X π hmin hDP hrank).Lweil =
        (1 / ((n : ℚ) - 2)) • (surface n a ha).picardTensorInclusion
          (FrobeniusMultiCentrePicardRealization.realization 1 n a
            (FrobeniusPicard.nefVector 2 n))) ∧
      IsLeast {d : ℚ | ∃ C : (surface n a ha).PrimeCurve,
        ¬ IsExceptionalCurve π C ∧ d = (datum n a ha X π hmin hDP hrank).Ldeg C}
        (1 / ((n : ℚ) - 2)) ∧
      (∀ i : Fin n, ¬ IsExceptionalCurve π (newestCurve n a ha i) ∧
        (datum n a ha X π hmin hDP hrank).Ldeg (newestCurve n a ha i) = 1 / ((n : ℚ) - 2)) ∧
      ((surface n a ha).rationalWeilToRationalPicard (surface_regularPoints n a ha)
          ((datum n a ha X π hmin hDP hrank).Lweil +
            (1 / ((n : ℚ) - 2)) • (surface n a ha).rationalCartierToWeilHom
              (datum n a ha X π hmin hDP hrank).KS) =
        (((n : ℚ) - 3) / ((n : ℚ) - 2)) •
          (surface n a ha).picardTensorInclusion (multiSecondFiberClass 2 n a)) ∧
      -- (4) the ruling of class `b`
      (∀ i : Fin n, multiSecondFiberClass 2 n a =
        cartierPicardHom (surface n a ha).toScheme (primeDivisor n a ha (.inr (.inl i))) +
          cartierPicardHom (surface n a ha).toScheme (primeDivisor n a ha (.inr (.inr i))) +
          (2 : ℤ) • cartierPicardHom (surface n a ha).toScheme
            ((surface n a ha).primeCurveCartier (surface_regularPoints n a ha)
              (newestCurve n a ha i))) ∧
      (∀ i : Fin n, (multiProjection 2 n a ≫ FrobeniusGraphClosed.secondProjection).base ⁻¹'
          {FrobeniusProjectivePoints.point (a i ^ 2)} =
        (primeCurve n a ha (.inr (.inl i)) : Set (surface n a ha).toScheme) ∪
          (primeCurve n a ha (.inr (.inr i)) : Set (surface n a ha).toScheme) ∪
          (newestCurve n a ha i : Set (surface n a ha).toScheme)) ∧
      (∀ z : projectiveSpace k 1, IsClosed ({z} : Set (projectiveSpace k 1)) →
        (∀ i : Fin n, z ≠ FrobeniusProjectivePoints.point (a i ^ 2)) →
        IsIrreducible ((multiProjection 2 n a ≫ FrobeniusGraphClosed.secondProjection).base ⁻¹'
          {z})) ∧
      -- (5) the purely inseparable bisection `B`
      ((primeCurve n a ha (.inl ()) : Set (surface n a ha).toScheme) =
        Set.range (FrobeniusMultiCentreGraphFiber.graphStrictι 2 n a).base ∧
      (letI : Algebra (projectiveSpace k 1).functionField
          (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField :=
        (functionFieldMap (FrobeniusActualStrictGraphInseparable.strictGraphRuling n a)).hom.toAlgebra
       letI : Module (projectiveSpace k 1).functionField
          (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField := Algebra.toModule
       Module.finrank (projectiveSpace k 1).functionField
        (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField = 2) ∧
      (letI : Algebra (projectiveSpace k 1).functionField
          (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField :=
        (functionFieldMap (FrobeniusActualStrictGraphInseparable.strictGraphRuling n a)).hom.toAlgebra
       IsPurelyInseparable (projectiveSpace k 1).functionField
        (FrobeniusMultiCentreGraphFiber.graphStrict 2 n a).functionField)) ∧
      -- (6) the code `DE(n)` of the `2n` isolated nodes
      (4 ≤ n → (primeCurve n a ha (.inl ())).selfIntersectionNumber
        (surface_regularPoints n a ha) < -2) ∧
      (∀ A B : Finset (Fin n),
        (∃ c : Additive (surface n a ha).toScheme.Pic,
          (2 : ℤ) • c = cartierPicardHom (surface n a ha).toScheme
            ((∑ i ∈ A, primeDivisor n a ha (.inr (.inl i))) +
              ∑ i ∈ B, primeDivisor n a ha (.inr (.inr i)))) ↔
          A = B ∧ Even A.card) ∧
      (∀ A : Finset (Fin n), Even A.card →
        (2 : ℤ) • (((A.card / 2 : ℕ) : ℤ) • multiSecondFiberClass 2 n a -
          ∑ i ∈ A, exceptionalClass 2 n a i (1 : Fin 2)) =
          cartierPicardHom (surface n a ha).toScheme
            ((∑ i ∈ A, primeDivisor n a ha (.inr (.inl i))) +
              ∑ i ∈ A, primeDivisor n a ha (.inr (.inr i)))) ∧
      (Finset.univ.filter (fun A : Finset (Fin n) => Even A.card)).card = 2 ^ (n - 1) ∧
      (∀ A B : Finset (Fin n), A = B → Even A.card → A ≠ ∅ → 4 ≤ A.card + B.card) := by
  have hn2 : 2 < n := by omega
  let a : Fin n → k := centers n
  have ha : Function.Injective a := centers_injective n
  letI : IsIntegral (multiSurface (1 + 1) n a) := multiSurface_isIntegral (1 + 1) n a ha
  obtain ⟨m, hm, X, π, hπ, hproper, hsurj, hbir, hc, hgeom,
      hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal,
      hKlt, hIsKlt, hsing, hcard, hcount⟩ :=
    exists_normal_projective_surface_rank_one_klt_exact_singular_count 1 n a ha hn2
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  have hDP : IsKltDelPezzo X :=
    (target_isKltDelPezzo_iff_parameters
      1 n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e hA).mpr (Or.inl rfl)
  refine ⟨a, ha, X, π, hminimal, hDP, hrank, hcard,
    datum_Lsq n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e hminimal hDP hrank,
    isExceptionalCurve_iff n a ha hn2 X π hπ hcriterion,
    primeCurve_injective n a ha,
    FrobeniusCharacteristicTwo.retainedLabel_card n,
    primeCurve_disjoint n a ha,
    primeCurve_intersectionNumber n a ha,
    ?_,
    node_selfIntersectionNumber n a ha,
    datum_Lweil_rationalPicard n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e hminimal hDP hrank,
    datum_Ldeg_isLeast n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e hminimal hDP hrank,
    fun i => ⟨newestCurve_not_exceptional n a ha X π hπ hcriterion i,
      datum_Ldeg_newestCurve n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e hminimal hDP
        hrank i⟩,
    datum_adjoint n a ha hn2 X π hπ hbir hpoints hcriterion A m hm e hminimal hDP hrank,
    secondFiberClass_eq n a ha,
    secondRuling_special_fiber_eq n a ha,
    secondRuling_fiber_irreducible n a,
    graph_inseparable_bisection n a ha,
    graph_selfIntersectionNumber_lt n a ha,
    code_even_iff n a ha,
    code_half_class n a ha,
    card_even_subsets n (by omega),
    fun A B hAB hA hne => code_min_weight A B hAB hA hne⟩
  rw [primeCurve_selfIntersectionNumber]
  rfl

end Existence

end KltDP.Manuscript.S10

#print axioms KltDP.Manuscript.S10.card_even_subsets
#print axioms KltDP.Manuscript.S10.isExceptionalCurve_iff
#print axioms KltDP.Manuscript.S10.code_even_iff
#print axioms KltDP.Manuscript.S10.datum_Ldeg_isLeast
#print axioms KltDP.Manuscript.S10.datum_adjoint
#print axioms KltDP.Manuscript.S10.datum_Lsq
#print axioms KltDP.Manuscript.S10.sevenNodes_code
#print axioms KltDP.Manuscript.S10.characteristicTwoFamily_code
