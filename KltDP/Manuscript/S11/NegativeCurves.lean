import KltDP.Manuscript.S10.FrobeniusFamily
import KltDP.Manuscript.S05.PicardIndex
import KltDP.Manuscript.S07.AdjointConfiguration
import KltDP.Manuscript.S02.Projection
import KltDP.Support.EqualityNumbers
import KltDP.Support.EqualityAdjointIdentities
import KltDP.Examples.FrobeniusMultiCentrePicardGeneration
import KltDP.Examples.FrobeniusMultiCentreCanonicalRetainedPairing
import KltDP.Examples.FrobeniusMultiCentreExceptionalSmooth
import KltDP.Geometry.PrimeCurvePairingSupport

/-!
# Proposition 11.1 (`prop:equality-negative-curves`, manuscript lines 3141–3261):
# the thirteen exterior negative curves of the seven-point surface

Setting (lines 3147–3154): `p = 3`, the seven-point surface `S = S_{3,3}` is the union's
multi-centre Frobenius source `sourceSurface 2 3 a ha _` for three distinct graph parameters
`a : Fin 3 → k` (`k` algebraically closed of characteristic three), with
`L = (B + b)/3`, `L² = 1/3`.

**Deviation from the manuscript.** The manuscript chooses the parameters `I = {0, 1, ∞}`
(so that everything is defined over `F₃`). The union's surface only admits *finite* selected
points `a_i ∈ k`; every statement below is for an arbitrary injective `a : Fin 3 → k`
(the curve equations of lines 3175–3179, which use the point at infinity, are not formalized).

Contents:

* **Lattice part** (`Vec = FrobeniusPicard.PicardVector 3 3 = ℤ¹¹`, basis `a, b, E_{ij}`): the
  thirteen classes `P_i = E_{i3}`, `T_i = a - E_{i1}`, `Θ = a + b - Σ E_{i1}`, `Q_i`, `W_i` of
  lines 3163–3170; all have square `-1` and `K·Z = -1`; their `L`-degrees `3L·Z = (B+b)·Z` are
  `1, 1, 2, 2, 3` (lines 3181–3185); the thirteen classes are distinct and are exactly the
  integral classes of the union's thirteen admissible contact patterns
  (`U-EQUALITY-CONTACT-CERT`); the label/index dictionary with `Support.EqualityNumbers`
  (`gram 2 3 = -negMatrix`, `newestGram = contactP`).
* **Geometry part** (actual curves on `S_{3,3}`): `P_i` is an exterior `(-1)`-curve
  (`≅ P¹`, `P_i² = -1`) of class `E_{i3}` with `L · P_i = 1/3`; for every prime curve with a
  known class, `L · C = (B+b)·C / 3`; the least exterior `L`-degree is `1/3`
  (every exterior prime curve has `L · C ≥ 1/3`), so every `P_i` is a *shortest* exterior
  `(-1)`-curve (`IsShortestExteriorMinusOne`); the exceptional vertices of the datum are the
  ten curves `B, F_i, U_i, V_i` (`labelEquiv`), with intersection matrix `gram 2 3`, so
  `A = negMatrixQ` up to the index equivalence.
* **Not formalized (isolated, see the end of the file):** the actual curves `T_i, Θ, Q_i, W_i`
  (the union has no strict vertical fibre through a centre, no diagonal, and no graph/cusp strict
  transforms on `S_{3,3}`), hence the completeness clause "exactly thirteen exterior negative
  curves, twenty-three negative curves in all" (lines 3186–3189, 3217–3260). Its arithmetic core
  is the union's `admissible_iff_mem_patterns`; the geometric input it needs is stated as the
  explicit hypothesis of `exterior_negative_class_mem_patterns_of`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Examples KltDP.Examples.FrobeniusMultiCentreSurface
open KltDP.Examples.FrobeniusMultiCentreIntegral KltDP.Examples.FrobeniusProjectivityProved
open KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
open KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives
open KltDP.Examples.FrobeniusMultiCentreContractingNef
open KltDP.Examples.FrobeniusMultiCentreContractingClass
open KltDP.Examples.FrobeniusMultiCentreExceptionalPrime
open KltDP.Examples.FrobeniusMultiCentreExceptionalSmooth
open KltDP.Examples.FrobeniusMultiCentrePicardRealization
open KltDP.Geometry.PrimeCurveClassPairing
open KltDP.Geometry.PrimeCurvePairingSupport
open KltDP.Geometry.InvertibleSheafSectionPowers
open KltDP.Manuscript KltDP.Manuscript.S10

universe u

namespace KltDP.Manuscript.S11

open KltDP.Support.EqualityNumbers (Index negMatrix negMatrixQ contactP contactT contactPQ
  contactTQ canonicalSource canonicalSourceQ weight)

/-! ### The label/index dictionary with `Support.EqualityNumbers` -/

/-- `B ↦ inl 0`, `F_i ↦ inl (i+1)`, `C_{ij} ↦ inr (j, i)` (`C_{i0} = U_i`, `C_{i1} = V_i`). -/
def toIndex : RetainedLabel 2 3 → Index
  | .inl _ => .inl 0
  | .inr (.inl i) => .inl i.succ
  | .inr (.inr (i, j)) => .inr (j, i)

def ofIndex : Index → RetainedLabel 2 3
  | .inl ⟨0, _⟩ => .inl ()
  | .inl ⟨m + 1, h⟩ => .inr (.inl ⟨m, by omega⟩)
  | .inr (j, i) => .inr (.inr (i, j))

theorem ofIndex_toIndex : ∀ l, ofIndex (toIndex l) = l := by decide
theorem toIndex_ofIndex : ∀ v, toIndex (ofIndex v) = v := by decide

/-- The retained labels of the seven-point surface are the ten indices of `EqualityNumbers`. -/
def labelIndexEquiv : RetainedLabel 2 3 ≃ Index :=
  ⟨toIndex, ofIndex, ofIndex_toIndex, toIndex_ofIndex⟩

@[simp] theorem labelIndexEquiv_apply (l : RetainedLabel 2 3) : labelIndexEquiv l = toIndex l := rfl

/-- The manuscript's negative intersection matrix of `D` (lines 3229–3230) is the union's
`negMatrix`: `-gram 2 3 l l' = negMatrix (toIndex l) (toIndex l')`. -/
theorem gram_eq_negMatrix : ∀ l l' : RetainedLabel 2 3,
    -(gram 2 3 l l') = negMatrix (toIndex l) (toIndex l') := by decide

/-- The contact row of `P_i` with `D` (`B, F_i, V_i` once each, line 3294). -/
theorem newestGram_eq_contactP : ∀ (l : RetainedLabel 2 3) (i : Fin 3),
    newestGram 2 3 l i = contactP i (toIndex l) := by decide

/-- The weights `3, 3, 3, 3, 2, …, 2`. -/
theorem gram_diag_eq_weight : ∀ l : RetainedLabel 2 3, -(gram 2 3 l l) = (weight (toIndex l) : ℤ) := by
  decide

/-! ### The thirteen classes in the lattice `ℤ¹¹ = ⟨a, b, E_{ij}⟩` -/

/-- The Picard lattice of `S_{3,3}` in the basis `a, b, E_{ij}` (`i, j : Fin 3`; `E_{i,j}` is the
manuscript's `E_{i,j+1}`). -/
abbrev Vec := FrobeniusPicard.PicardVector 3 3

/-- The total transform `E_{i,j+1}` of the `j`-th exceptional curve of the `i`-th cluster. -/
def E (i j : Fin 3) : Vec := FrobeniusPicard.exceptional (i, j)

/-- `P_i = E_{i3}` (the newest exceptional curve). -/
def Pvec (i : Fin 3) : Vec := E i 2

/-- `T_i = a - E_{i1}` (line 3165). -/
def Tvec (i : Fin 3) : Vec := FrobeniusPicard.a - E i 0

/-- `Θ = a + b - Σ_i E_{i1}` (line 3165). -/
def thetaVec : Vec := FrobeniusPicard.a + FrobeniusPicard.b - (E 0 0 + E 1 0 + E 2 0)

/-- `Q_i = 2a + b - E_{i1} - Σ_{j ≠ i} (E_{j1} + E_{j2})` (line 3166). -/
def Qvec (i : Fin 3) : Vec :=
  (2, 1, fun jl => if jl.1 = i then (if jl.2 = 0 then -1 else 0) else (if jl.2 = 2 then 0 else -1))

/-- `W_i = 3a + 2b - (E_{i1} + E_{i2} + E_{i3}) - Σ_{j ≠ i} (2E_{j1} + E_{j2})` (lines 3167–3168). -/
def Wvec (i : Fin 3) : Vec :=
  (3, 2, fun jl => if jl.1 = i then -1 else (if jl.2 = 0 then -2 else if jl.2 = 1 then -1 else 0))

/-- `K_S = -2a - 2b + Σ E_{ij}` (line 3300). -/
abbrev Kvec : Vec := FrobeniusPicard.canonicalVector 3 3

/-- `3L = B + b = 3a + 2b - Σ E_{ij}` (line 3151; the union's `nefVector 3 3`). -/
abbrev Mvec : Vec := FrobeniusPicard.nefVector 3 3

theorem Qvec_formula (i : Fin 3) :
    Qvec i = 2 • FrobeniusPicard.a + FrobeniusPicard.b - E i 0 -
      ∑ j ∈ Finset.univ.erase i, (E j 0 + E j 1) := by
  fin_cases i <;> decide

theorem Wvec_formula (i : Fin 3) :
    Wvec i = 3 • FrobeniusPicard.a + 2 • FrobeniusPicard.b - (E i 0 + E i 1 + E i 2) -
      ∑ j ∈ Finset.univ.erase i, (2 • E j 0 + E j 1) := by
  fin_cases i <;> decide

theorem Mvec_eq : Mvec = FrobeniusPicard.graphVector 3 3 + FrobeniusPicard.b := by decide

/-- The thirteen classes are the integral classes of the union's thirteen admissible contact
patterns (`KltDP.Support.integralClass`, `U-EQUALITY-CONTACT-CERT`). -/
def ofClassVector (x : KltDP.Support.ClassVector) : Vec := (x.a, x.b, fun ij => x.e ij.1 ij.2)

theorem ofClassVector_patterns :
    (∀ i, ofClassVector (KltDP.Support.integralClass (KltDP.EqualityContacts.P i)) = Pvec i) ∧
    (∀ i, ofClassVector (KltDP.Support.integralClass (KltDP.EqualityContacts.T i)) = Tvec i) ∧
    ofClassVector (KltDP.Support.integralClass KltDP.EqualityContacts.theta) = thetaVec ∧
    (∀ i, ofClassVector (KltDP.Support.integralClass (KltDP.EqualityContacts.Q i)) = Qvec i) ∧
    (∀ i, ofClassVector (KltDP.Support.integralClass (KltDP.EqualityContacts.W i)) = Wvec i) := by
  decide

/-- All thirteen classes have square `-1` (line 3162, 3214). -/
theorem thirteen_squares :
    (∀ i, FrobeniusPicard.pairing (Pvec i) (Pvec i) = -1) ∧
    (∀ i, FrobeniusPicard.pairing (Tvec i) (Tvec i) = -1) ∧
    FrobeniusPicard.pairing thetaVec thetaVec = -1 ∧
    (∀ i, FrobeniusPicard.pairing (Qvec i) (Qvec i) = -1) ∧
    (∀ i, FrobeniusPicard.pairing (Wvec i) (Wvec i) = -1) := by decide

/-- All thirteen classes have `K_S · Z = -1` (adjunction for a smooth rational `(-1)`-curve). -/
theorem thirteen_canonical :
    (∀ i, FrobeniusPicard.pairing Kvec (Pvec i) = -1) ∧
    (∀ i, FrobeniusPicard.pairing Kvec (Tvec i) = -1) ∧
    FrobeniusPicard.pairing Kvec thetaVec = -1 ∧
    (∀ i, FrobeniusPicard.pairing Kvec (Qvec i) = -1) ∧
    (∀ i, FrobeniusPicard.pairing Kvec (Wvec i) = -1) := by decide

/-- The `L`-degrees, cleared of the denominator `3`: `3 L · Z = (B + b) · Z` is `1, 1, 2, 2, 3`
(lines 3181–3185). -/
theorem thirteen_degrees :
    (∀ i, FrobeniusPicard.pairing Mvec (Pvec i) = 1) ∧
    (∀ i, FrobeniusPicard.pairing Mvec (Tvec i) = 1) ∧
    FrobeniusPicard.pairing Mvec thetaVec = 2 ∧
    (∀ i, FrobeniusPicard.pairing Mvec (Qvec i) = 2) ∧
    (∀ i, FrobeniusPicard.pairing Mvec (Wvec i) = 3) := by decide

/-- Contacts with the ten retained classes: `P_i` meets `B, F_i, V_i`; `T_i` meets `F_j, F_k, U_i`
(lines 3290–3296); `Θ` meets `B` and every `U_i`; `Q_i` meets `F_i, U_i` and `V_j` (`j ≠ i`);
`W_i` meets `U_j, V_j` (`j ≠ i`), all once. -/
theorem thirteen_contacts :
    (∀ (l : RetainedLabel 2 3) (i : Fin 3),
      FrobeniusPicard.pairing (retainedVector 2 3 l) (Pvec i) = contactP i (toIndex l)) ∧
    (∀ (l : RetainedLabel 2 3) (i : Fin 3),
      FrobeniusPicard.pairing (retainedVector 2 3 l) (Tvec i) = contactT i (toIndex l)) ∧
    (∀ l : RetainedLabel 2 3, FrobeniusPicard.pairing (retainedVector 2 3 l) thetaVec =
      match l with
      | .inl _ => 1
      | .inr (.inl _) => 0
      | .inr (.inr (_, j)) => if j = 0 then 1 else 0) ∧
    (∀ (l : RetainedLabel 2 3) (i : Fin 3),
      FrobeniusPicard.pairing (retainedVector 2 3 l) (Qvec i) =
      match l with
      | .inl _ => 0
      | .inr (.inl i') => if i' = i then 1 else 0
      | .inr (.inr (i', j)) => if i' = i then (if j = 0 then 1 else 0) else (if j = 1 then 1 else 0)) ∧
    (∀ (l : RetainedLabel 2 3) (i : Fin 3),
      FrobeniusPicard.pairing (retainedVector 2 3 l) (Wvec i) =
      match l with
      | .inl _ => 0
      | .inr (.inl _) => 0
      | .inr (.inr (i', _)) => if i' = i then 0 else 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The thirteen classes are pairwise distinct (line 3257). -/
theorem thirteen_distinct :
    ({Pvec 0, Pvec 1, Pvec 2, Tvec 0, Tvec 1, Tvec 2, thetaVec, Qvec 0, Qvec 1, Qvec 2,
      Wvec 0, Wvec 1, Wvec 2} : Finset Vec).card = 13 := by decide

/-! ### The seven-point surface and its actual curves -/

section Geometry

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 3]

local instance factPrimeThree : Fact (2 + 1).Prime := ⟨Nat.prime_three⟩

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

variable (a : Fin 3 → k) (ha : Function.Injective a)

/-- Projectivity of the seven-point surface (the union's theorem). -/
abbrev sevenProj : IsProjectiveOverField (multiStructure (2 + 1) 3 a) :=
  originalMultiStructureProjective k (2 + 1) 3 a

/-- The seven-point surface `S = S_{3,3}`: the union's multi-centre Frobenius source at `p = 3`,
`n = 3` (three graph blowups at each of the three selected graph points `(a_i, a_i³)`). -/
abbrev sevenSurface : NormalProjectiveSurface k := sourceSurface 2 3 a ha (sevenProj a)

/-- Regularity of the seven-point surface. -/
abbrev sevenRegular : ∀ x : (sevenSurface a ha).Point,
    RegularPoint (sevenSurface a ha).toScheme x := sourceRegular 2 3 a ha

/-- The additive Picard class of a prime curve. -/
abbrev curveClass (C : (sevenSurface a ha).PrimeCurve) : Additive (sevenSurface a ha).toScheme.Pic :=
  cartierPicardHom (sevenSurface a ha).toScheme
    ((sevenSurface a ha).primeCurveCartier (sevenRegular a ha) C)

/-- `M = B + b` (the union's contracting divisor); `3L ∼ M`. -/
abbrev Mdiv : CartierDivisor (sevenSurface a ha).toScheme :=
  contractingDivisor 2 3 a ha (sevenProj a)

/-- The union's canonical Cartier divisor `K_S` of the seven-point surface. -/
abbrev Kdiv : CartierDivisor (sevenSurface a ha).toScheme := canonicalCartier 2 3 a ha (sevenProj a)

/-- Intersection numbers of curves and divisors with known classes are computed in the lattice. -/
theorem intersectionNumber_of_classes (C : (sevenSurface a ha).PrimeCurve)
    (D : CartierDivisor (sevenSurface a ha).toScheme) (x y : Vec)
    (hC : curveClass a ha C = realization 2 3 a x)
    (hD : cartierPicardHom (sevenSurface a ha).toScheme D = realization 2 3 a y) :
    C.intersectionNumber D = FrobeniusPicard.pairing x y := by
  rw [← PrimeCurve.picardRestrictionDegreeHom_cartierPicardHom,
    ← pairing_primeCurve_left (sevenSurface a ha) (sevenRegular a ha)]
  change pairing (sevenSurface a ha) (sevenRegular a ha) (curveClass a ha C)
    (cartierPicardHom (sevenSurface a ha).toScheme D) = _
  rw [hC, hD]
  exact realization_preserves_pairing 2 3 a ha (sevenProj a) x y

theorem retainedCurve_class (l : RetainedLabel 2 3) :
    curveClass a ha (retainedCurve 2 3 a ha l) = realization 2 3 a (retainedVector 2 3 l) :=
  retainedCurve_cartierClass 2 3 a ha l

omit [CharP k 3] in
/-- The class of `P_i` is `E_{i3}`. -/
theorem newestCurveP_class (i : Fin 3) :
    curveClass a ha (newestCurveP 2 3 a ha i) = realization 2 3 a (Pvec i) :=
  newestCurveP_cartierClass 2 3 a ha i

/-- The class of `K_S` is `-2a - 2b + Σ E_{ij}`. -/
theorem Kdiv_class :
    cartierPicardHom (sevenSurface a ha).toScheme (Kdiv a ha) = realization 2 3 a Kvec := by
  rw [Kdiv, canonicalCartier_picard]
  exact FrobeniusMultiCentreCanonicalRetainedPairing.multiCanonicalClass_eq_realization 2 3 a ha

/-- The class of `M = B + b` is `3a + 2b - Σ E_{ij}`. -/
theorem Mdiv_class :
    cartierPicardHom (sevenSurface a ha).toScheme (Mdiv a ha) = realization 2 3 a Mvec := by
  rw [Mdiv, contractingDivisor_class, contractingClass_eq_realization]

/-- `P_i` is a `(-1)`-curve: it is isomorphic to `P¹` over `k` and `P_i² = -1`. -/
theorem newestCurveP_isMinusOne (i : Fin 3) :
    IsMinusOneCurve (sevenRegular a ha) (newestCurveP 2 3 a ha i) := by
  refine ⟨⟨exceptionalPrimeProjectiveLineIso 2 3 a ha i (.inr PUnit.unit) (sevenProj a),
    exceptionalPrimeProjectiveLineIso_hom_structure 2 3 a ha i (.inr PUnit.unit) (sevenProj a)⟩, ?_⟩
  change (newestCurveP 2 3 a ha i).intersectionNumber
    ((sevenSurface a ha).primeCurveCartier (sevenRegular a ha) (newestCurveP 2 3 a ha i)) = -1
  rw [newestCurveP_intersectionNumber, if_pos rfl]

omit [CharP k 3] in
/-- `P_i` is smooth over `k`. -/
theorem newestCurveP_isSmooth (i : Fin 3) : IsSmooth (newestCurveP 2 3 a ha i).toSpec :=
  exceptionalPrime_isSmooth_toSpec 2 3 a ha i (.inr PUnit.unit) (sevenProj a)

/-- `M · P_i = 1`, `M · B = M · F_i = M · C_{ij} = 0`. -/
theorem Mdiv_intersection :
    (∀ i : Fin 3, (newestCurveP 2 3 a ha i).intersectionNumber (Mdiv a ha) = 1) ∧
    (∀ l : RetainedLabel 2 3, (retainedCurve 2 3 a ha l).intersectionNumber (Mdiv a ha) = 0) := by
  refine ⟨fun i => ?_, fun l => ?_⟩
  · rw [intersectionNumber_of_classes a ha _ _ (Pvec i) Mvec (newestCurveP_class a ha i)
      (Mdiv_class a ha)]
    rw [FrobeniusPicard.pairing_comm]
    exact thirteen_degrees.1 i
  · rw [intersectionNumber_of_classes a ha _ _ (retainedVector 2 3 l) Mvec
      (retainedCurve_class a ha l) (Mdiv_class a ha)]
    revert l; decide

/-- `K_S · P_i = -1` and `K_S · B = K_S · F_i = 1`, `K_S · C_{ij} = 0` (the canonical degrees
`b_i - 2` of the exceptional curves). -/
theorem Kdiv_intersection :
    (∀ i : Fin 3, (newestCurveP 2 3 a ha i).intersectionNumber (Kdiv a ha) = -1) ∧
    (∀ l : RetainedLabel 2 3, (retainedCurve 2 3 a ha l).intersectionNumber (Kdiv a ha) =
      (weight (toIndex l) : ℤ) - 2) := by
  refine ⟨fun i => ?_, fun l => ?_⟩
  · rw [intersectionNumber_of_classes a ha _ _ (Pvec i) Kvec (newestCurveP_class a ha i)
      (Kdiv_class a ha)]
    rw [FrobeniusPicard.pairing_comm]
    exact thirteen_canonical.1 i
  · rw [intersectionNumber_of_classes a ha _ _ (retainedVector 2 3 l) Kvec
      (retainedCurve_class a ha l) (Kdiv_class a ha)]
    revert l; decide

/-! ### The resolution datum of a contraction of the seven-point surface -/

variable (Y : NormalProjectiveSurface k) (π : (sevenSurface a ha).toScheme ⟶ Y.toScheme)
    (hπ : π ≫ Y.structureMorphism = multiStructure (2 + 1) 3 a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (sevenSurface a ha).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine 2 3 a ha) = 0)
    (hmin : IsMinimalResolution (sevenSurface a ha) Y π) (hDP : IsKltDelPezzo Y)
    (hrank : Y.picardRank = 1)

/-- The resolution datum `(S_{3,3}, X, π)` of the seven-point surface (a `def`, so that the
instances on `(datum …).Vertices` are found). -/
def datum : ResolutionDatum k := ⟨sevenSurface a ha, Y, π, hmin, hDP, hrank⟩

omit [CharP k 3] in
@[simp] theorem datum_S : (datum a ha Y π hmin hDP hrank).S = sevenSurface a ha := rfl
omit [CharP k 3] in
@[simp] theorem datum_X : (datum a ha Y π hmin hDP hrank).X = Y := rfl
omit [CharP k 3] in
@[simp] theorem datum_π : (datum a ha Y π hmin hDP hrank).π = π := rfl

include hπ hcriterion in
/-- `P_i` is an exterior `(-1)`-curve of the datum. -/
theorem newestCurveP_isExteriorMinusOne (i : Fin 3) :
    (datum a ha Y π hmin hDP hrank).IsExteriorMinusOne (newestCurveP 2 3 a ha i) :=
  ⟨newestCurveP_isMinusOne a ha i, newestCurveP_not_exceptional 2 3 a ha Y π hπ hcriterion i⟩

include hπ hcriterion in
/-- The exceptional curves of the datum are exactly the ten curves `B, F_i, U_i, V_i`. -/
theorem isExceptionalCurve_iff (C : (sevenSurface a ha).PrimeCurve) :
    IsExceptionalCurve π C ↔ ∃ l : RetainedLabel 2 3, C = retainedCurve 2 3 a ha l :=
  isExceptionalCurve_iff_retained 2 3 a ha (by norm_num) Y π hπ hcriterion C

include hπ hcriterion in
/-- The vertex of the exceptional graph carried by a retained label. -/
def vertexOfLabel (l : RetainedLabel 2 3) : (datum a ha Y π hmin hDP hrank).Vertices :=
  ⟨retainedCurve 2 3 a ha l, (isExceptionalCurve_iff a ha Y π hπ hcriterion _).mpr ⟨l, rfl⟩⟩

include hπ hcriterion in
theorem vertexOfLabel_bijective :
    Function.Bijective (vertexOfLabel a ha Y π hπ hcriterion hmin hDP hrank) := by
  refine ⟨fun l l' h => retainedCurve_injective 2 3 a ha (by norm_num) (congrArg Subtype.val h),
    fun v => ?_⟩
  obtain ⟨l, hl⟩ := (isExceptionalCurve_iff a ha Y π hπ hcriterion v.val).mp v.property
  exact ⟨l, Subtype.ext hl.symm⟩

include hπ hcriterion in
/-- **The ten vertices**: `RetainedLabel 2 3 ≃ R.Vertices`. -/
def labelEquiv : RetainedLabel 2 3 ≃ (datum a ha Y π hmin hDP hrank).Vertices :=
  Equiv.ofBijective _ (vertexOfLabel_bijective a ha Y π hπ hcriterion hmin hDP hrank)

include hπ hcriterion in
theorem labelEquiv_apply_val (l : RetainedLabel 2 3) :
    (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank l).val = retainedCurve 2 3 a ha l := rfl

include hπ hcriterion in
/-- `R.Vertices ≃ EqualityNumbers.Index`. -/
def vertexIndex : (datum a ha Y π hmin hDP hrank).Vertices ≃ Index :=
  (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank).symm.trans labelIndexEquiv

include hπ hcriterion in
theorem vertexIndex_labelEquiv (l : RetainedLabel 2 3) :
    vertexIndex a ha Y π hπ hcriterion hmin hDP hrank
      (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank l) = toIndex l := by
  simp [vertexIndex]

include hπ hcriterion in
/-- Ten original exceptional components (line 3339). -/
theorem card_vertices : Fintype.card (datum a ha Y π hmin hDP hrank).Vertices = 10 := by
  rw [← Fintype.card_congr (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank), retainedLabel_card]

include hπ hcriterion in
/-- The intersection matrix of the exceptional curves is `gram 2 3`. -/
theorem M_labelEquiv (l l' : RetainedLabel 2 3) :
    (datum a ha Y π hmin hDP hrank).M (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank l)
      (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank l') = (gram 2 3 l l' : ℚ) := by
  change ((sevenSurface a ha).intersectionPairing (sevenRegular a ha)
    ((sevenSurface a ha).primeCurveCartier (sevenRegular a ha) (retainedCurve 2 3 a ha l))
    ((sevenSurface a ha).primeCurveCartier (sevenRegular a ha) (retainedCurve 2 3 a ha l')) : ℚ) = _
  rw [intersectionPairing_primeCurves_eq_intersectionNumber, retainedCurve_intersectionNumber]

include hπ hcriterion in
/-- **`A_D = negMatrixQ`** up to the index equivalence: the negative intersection matrix of the
datum is the manuscript's four `[3]` blocks and three `A₂` blocks (lines 3229–3230). -/
theorem A_eq_submatrix :
    (datum a ha Y π hmin hDP hrank).A =
      negMatrixQ.submatrix (vertexIndex a ha Y π hπ hcriterion hmin hDP hrank)
        (vertexIndex a ha Y π hπ hcriterion hmin hDP hrank) := by
  ext i j
  obtain ⟨l, rfl⟩ := (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank).surjective i
  obtain ⟨l', rfl⟩ := (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank).surjective j
  rw [ResolutionDatum.A, Matrix.neg_apply, M_labelEquiv, Matrix.submatrix_apply,
    vertexIndex_labelEquiv, vertexIndex_labelEquiv, KltDP.Support.EqualityNumbers.negMatrixQ_eq_map,
    Matrix.map_apply, ← gram_eq_negMatrix]
  push_cast
  ring

include hπ hcriterion in
/-- The weights `b_i = -D_i²`: `3` on `B, F_i`, `2` on `U_i, V_i`. -/
theorem w_labelEquiv (l : RetainedLabel 2 3) :
    (datum a ha Y π hmin hDP hrank).w (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank l) =
      (weight (toIndex l) : ℚ) := by
  rw [ResolutionDatum.w, M_labelEquiv, ← Int.cast_neg, gram_diag_eq_weight]
  norm_cast

include hπ hcriterion in
/-- The contact vector of `P_i` with `D` is the manuscript's row `contactP i` (`B, F_i, V_i`). -/
theorem contact_newest (i : Fin 3) :
    KltDP.Manuscript.S05.contact (datum a ha Y π hmin hDP hrank) (newestCurveP 2 3 a ha i) =
      fun v => contactPQ i (vertexIndex a ha Y π hπ hcriterion hmin hDP hrank v) := by
  funext v
  obtain ⟨l, rfl⟩ := (labelEquiv a ha Y π hπ hcriterion hmin hDP hrank).surjective v
  rw [vertexIndex_labelEquiv]
  change ((newestCurveP 2 3 a ha i).intersectionNumber
    ((sevenSurface a ha).primeCurveCartier (sevenRegular a ha) (retainedCurve 2 3 a ha l)) : ℚ) = _
  rw [intersectionNumber_of_classes a ha _ _ (Pvec i) (retainedVector 2 3 l)
    (newestCurveP_class a ha i) (retainedCurve_class a ha l), FrobeniusPicard.pairing_comm,
    thirteen_contacts.1 l i]
  rfl

variable [IsProper π] [Surjective π] [IsIso π.c]
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine 2 3 a ha) m).obj)

/-! ### `L`-degrees on the datum -/

include hπ hbir hconnected hcriterion hm e in
/-- `L = π^*(-K_X) ∼_ℚ M/3 = (B + b)/3` (line 3151). -/
theorem datum_Lweil_classMap :
    (sevenSurface a ha).rationalWeilClassMap (datum a ha Y π hmin hDP hrank).Lweil =
      (1 / 3 : ℚ) • (sevenSurface a ha).rationalWeilClassMap
        ((sevenSurface a ha).rationalCartierToWeilHom (Mdiv a ha)) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  have hn : 2 < 3 := by norm_num
  set R : ResolutionDatum k := datum a ha Y π hmin hDP hrank with hR
  let K0 : Y.WeilDivisor := targetCanonicalWeil 2 3 a ha hn Y π hπ hbir hconnected hcriterion
  have hK0canon : IsCanonicalWeilDivisor Y K0 :=
    targetCanonicalWeil_isCanonical 2 3 a ha hn Y π hπ hbir hconnected hcriterion
  have hK0qc : Y.QCartier (rationalizeWeilDivisor Y K0) :=
    FrobeniusMultiCentreTargetQCartier.targetCanonicalWeil_qCartier
      2 3 a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  have hlin : Y.LinearlyEquivalent R.KX K0 :=
    IsCanonicalWeilDivisor.linearlyEquivalent R.KX_klt.1 hK0canon
  have hclass1 : (sevenSurface a ha).rationalWeilClassMap R.pullbackKX =
      (sevenSurface a ha).rationalWeilClassMap
        (QCartierPullback.pullback (X := sevenSurface a ha) (Y := Y) π
          (rationalizeWeilDivisor Y K0) hK0qc) :=
    ((sevenSurface a ha).rationalWeilClassMap_eq_iff _ _).mpr
      (QCartierPullback.pullback_qLinearlyEquivalent (X := sevenSurface a ha) (Y := Y) π _ _
        R.KX_qCartier hK0qc (Y.qLinearlyEquivalent_of_linearlyEquivalent hlin))
  have hanti : (sevenSurface a ha).rationalWeilClassMap
      (-QCartierPullback.pullback (X := sevenSurface a ha) (Y := Y) π
        (rationalizeWeilDivisor Y K0) hK0qc) =
      ((2 - (((2 + 1 : ℕ) : ℚ) - 2) * (((3 : ℕ) : ℚ) - 2)) /
        (((2 + 1 : ℕ) : ℚ) * (((3 : ℕ) : ℚ) - 2))) •
        (sevenSurface a ha).rationalWeilClassMap
          ((sevenSurface a ha).rationalCartierToWeilHom (Mdiv a ha)) :=
    anticanonical_pullback_classMap 2 3 a ha hn Y π hπ hbir hconnected hcriterion A m hm e hK0qc
  rw [map_neg] at hanti
  change (sevenSurface a ha).rationalWeilClassMap (-R.pullbackKX) = _
  rw [map_neg, hclass1, hanti]
  congr 1
  norm_num

include hπ hbir hconnected hcriterion hm e in
/-- `L · C = (M · C)/3 = ((B + b) · C)/3` for every prime curve `C`. -/
theorem datum_Ldeg_eq (C : (sevenSurface a ha).PrimeCurve) :
    (datum a ha Y π hmin hDP hrank).Ldeg C = (1 / 3 : ℚ) * (C.intersectionNumber (Mdiv a ha) : ℚ) := by
  set R : ResolutionDatum k := datum a ha Y π hmin hDP hrank with hR
  have hclass := datum_Lweil_classMap a ha Y π hπ hbir hconnected hcriterion hmin hDP hrank A m hm e
  have hnum : R.S.rationalWeilNumericalMap R.hreg R.Lweil =
      (1 / 3 : ℚ) • R.S.rationalWeilNumericalMap R.hreg
        (R.S.rationalCartierToWeilHom (Mdiv a ha)) := by
    rw [← R.S.rationalWeilClassNumericalMap_class R.hreg,
      ← R.S.rationalWeilClassNumericalMap_class R.hreg, ← map_smul]
    exact congrArg _ hclass
  change RationalWeilIntersection.degreeLinearMap R.S R.hreg C R.Lweil = _
  rw [← R.numericalRestrictionDegree_rationalWeilNumericalMap C R.Lweil, hnum, map_smul,
    smul_eq_mul, R.numericalRestrictionDegree_rationalWeilNumericalMap,
    RationalWeilIntersection.degreeLinearMap_rationalCartier]

include hπ hbir hconnected hcriterion hm e in
/-- `L · C = ((B + b) · [C])/3` for a prime curve of known class. -/
theorem datum_Ldeg_of_class (C : (sevenSurface a ha).PrimeCurve) (x : Vec)
    (hC : curveClass a ha C = realization 2 3 a x) :
    (datum a ha Y π hmin hDP hrank).Ldeg C = (FrobeniusPicard.pairing Mvec x : ℚ) / 3 := by
  rw [datum_Ldeg_eq a ha Y π hπ hbir hconnected hcriterion hmin hDP hrank A m hm e C,
    intersectionNumber_of_classes a ha C _ x Mvec hC (Mdiv_class a ha), FrobeniusPicard.pairing_comm]
  ring

include hπ hbir hconnected hcriterion hm e in
/-- `L · P_i = 1/3` (line 3183). -/
theorem datum_Ldeg_newest (i : Fin 3) :
    (datum a ha Y π hmin hDP hrank).Ldeg (newestCurveP 2 3 a ha i) = 1 / 3 := by
  rw [datum_Ldeg_of_class a ha Y π hπ hbir hconnected hcriterion hmin hDP hrank A m hm e _ _
    (newestCurveP_class a ha i), thirteen_degrees.1 i]
  norm_num

include hπ hbir hconnected hcriterion hm e in
/-- **The least exterior degree is `1/3`** (lines 3186–3188, proved without the nef threshold or
the seven-point bound): `M = B + b` is nef and integral and vanishes exactly on the curves of
`D`, so every exterior prime curve has `M · C ≥ 1`, i.e. `L · C ≥ 1/3`. -/
theorem datum_Ldeg_exterior_ge (C : (sevenSurface a ha).PrimeCurve)
    (hC : ¬ IsExceptionalCurve π C) : 1 / 3 ≤ (datum a ha Y π hmin hDP hrank).Ldeg C := by
  rw [datum_Ldeg_eq a ha Y π hπ hbir hconnected hcriterion hmin hDP hrank A m hm e C]
  have hnef : Positivity.IsNef (multiStructure (2 + 1) 3 a) (originalLine 2 3 a ha) :=
    contractingLine_isNef 2 3 a ha (sevenProj a) (by norm_num)
  have hnonneg : 0 ≤ C.restrictionDegree (originalLine 2 3 a ha) :=
    (Positivity.isNef_iff_forall_primeCurve (sevenSurface a ha) _).mp hnef C
  have hne : C.restrictionDegree (originalLine 2 3 a ha) ≠ 0 := by
    intro h0
    obtain ⟨p, hp, -⟩ := (hcriterion C).mpr h0
    exact hC (IsExceptionalCurve.of_fieldPoint_factor π C p hp)
  have h1 : (1 : ℤ) ≤ C.intersectionNumber (Mdiv a ha) := by
    change (1 : ℤ) ≤ C.restrictionDegree (originalLine 2 3 a ha)
    omega
  have h1' : (1 : ℚ) ≤ (C.intersectionNumber (Mdiv a ha) : ℚ) := by exact_mod_cast h1
  linarith

include hπ hbir hconnected hcriterion hm e in
/-- `ℓ_ext = 1/3`, attained by every `P_i`. -/
theorem datum_Ldeg_isLeast :
    IsLeast {d : ℚ | ∃ C : (sevenSurface a ha).PrimeCurve,
      ¬ IsExceptionalCurve π C ∧ d = (datum a ha Y π hmin hDP hrank).Ldeg C} (1 / 3) :=
  ⟨⟨newestCurveP 2 3 a ha 0, newestCurveP_not_exceptional 2 3 a ha Y π hπ hcriterion 0,
      (datum_Ldeg_newest a ha Y π hπ hbir hconnected hcriterion hmin hDP hrank A m hm e 0).symm⟩,
    fun d ⟨C, hC, hd⟩ => hd ▸
      datum_Ldeg_exterior_ge a ha Y π hπ hbir hconnected hcriterion hmin hDP hrank A m hm e C hC⟩

include hπ hbir hconnected hcriterion hm e in
/-- Every `P_i` is a *shortest* exterior `(-1)`-curve of the datum (line 3186–3187). -/
theorem newestCurveP_isShortest (i : Fin 3) :
    (datum a ha Y π hmin hDP hrank).IsShortestExteriorMinusOne (newestCurveP 2 3 a ha i) := by
  refine ⟨newestCurveP_isExteriorMinusOne a ha Y π hπ hcriterion hmin hDP hrank i, fun Q hQ => ?_⟩
  rw [datum_Ldeg_newest a ha Y π hπ hbir hconnected hcriterion hmin hDP hrank A m hm e i]
  exact datum_Ldeg_exterior_ge a ha Y π hπ hbir hconnected hcriterion hmin hDP hrank A m hm e Q hQ.2

end Geometry

/-! ### The proposition, assembled from the union's existence theorem -/

section Existence

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 3]

local instance factPrimeThreeE : Fact (2 + 1).Prime := ⟨Nat.prime_three⟩

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

/-- **Proposition 11.1, formalized part.** For every choice of three distinct graph parameters
`a : Fin 3 → k`, the union's contraction `π : S_{3,3} → X` of the seven-point surface gives a
resolution datum with: seven singular points, `L² = 1/3`; the ten exceptional curves
`B, F_i, U_i, V_i` (`Fintype.card R.Vertices = 10`) with negative intersection matrix
`negMatrixQ` (four `[3]` and three `A₂` blocks); the three curves `P_i = E_{i3}` are smooth
rational exterior `(-1)`-curves with `L · P_i = 1/3`, contact row `B, F_i, V_i`, and they are
shortest exterior `(-1)`-curves; the least exterior `L`-degree is `1/3`. -/
theorem sevenPointNegativeCurves (a : Fin 3 → k) (ha : Function.Injective a) :
    ∃ (X : NormalProjectiveSurface k) (π : (sevenSurface a ha).toScheme ⟶ X.toScheme)
      (hmin : IsMinimalResolution (sevenSurface a ha) X π) (hDP : IsKltDelPezzo X)
      (hrank : X.picardRank = 1),
      X.singularPoints.card = 7 ∧
      (datum a ha X π hmin hDP hrank).Lsq = 1 / 3 ∧
      Fintype.card (datum a ha X π hmin hDP hrank).Vertices = 10 ∧
      (∀ C : (sevenSurface a ha).PrimeCurve, IsExceptionalCurve π C ↔
        ∃ l : RetainedLabel 2 3, C = retainedCurve 2 3 a ha l) ∧
      (∃ ι : (datum a ha X π hmin hDP hrank).Vertices ≃ Index,
        (datum a ha X π hmin hDP hrank).A = negMatrixQ.submatrix ι ι ∧
        ∀ i : Fin 3, KltDP.Manuscript.S05.contact (datum a ha X π hmin hDP hrank)
          (newestCurveP 2 3 a ha i) = fun v => contactPQ i (ι v)) ∧
      (∀ i : Fin 3,
        IsSmooth (newestCurveP 2 3 a ha i).toSpec ∧
        (datum a ha X π hmin hDP hrank).IsExteriorMinusOne (newestCurveP 2 3 a ha i) ∧
        curveClass a ha (newestCurveP 2 3 a ha i) = realization 2 3 a (Pvec i) ∧
        (datum a ha X π hmin hDP hrank).Ldeg (newestCurveP 2 3 a ha i) = 1 / 3 ∧
        (datum a ha X π hmin hDP hrank).IsShortestExteriorMinusOne (newestCurveP 2 3 a ha i)) ∧
      IsLeast {d : ℚ | ∃ C : (sevenSurface a ha).PrimeCurve,
        ¬ IsExceptionalCurve π C ∧ d = (datum a ha X π hmin hDP hrank).Ldeg C} (1 / 3) := by
  have hn : 2 < 3 := by norm_num
  letI : IsIntegral (multiSurface (2 + 1) 3 a) := multiSurface_isIntegral (2 + 1) 3 a ha
  obtain ⟨m, hm, X, π, hπ, hproper, hsurj, hbir, hc, hgeom,
      hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal,
      hKlt, hIsKlt, hsing, hcard, hcount⟩ :=
    exists_normal_projective_surface_rank_one_klt_exact_singular_count 2 3 a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  have hDP : IsKltDelPezzo X :=
    (target_isKltDelPezzo_iff_parameters 2 3 a ha hn X π hπ hbir hpoints hcriterion A m hm e hA).mpr
      (Or.inr ⟨rfl, rfl⟩)
  refine ⟨X, π, hminimal, hDP, hrank, hcard, ?_,
    card_vertices a ha X π hπ hcriterion hminimal hDP hrank,
    isExceptionalCurve_iff a ha X π hπ hcriterion,
    ⟨vertexIndex a ha X π hπ hcriterion hminimal hDP hrank,
      A_eq_submatrix a ha X π hπ hcriterion hminimal hDP hrank,
      contact_newest a ha X π hπ hcriterion hminimal hDP hrank⟩,
    fun i => ⟨newestCurveP_isSmooth a ha i,
      newestCurveP_isExteriorMinusOne a ha X π hπ hcriterion hminimal hDP hrank i,
      newestCurveP_class a ha i,
      datum_Ldeg_newest a ha X π hπ hbir hpoints hcriterion hminimal hDP hrank A m hm e i,
      newestCurveP_isShortest a ha X π hπ hbir hpoints hcriterion hminimal hDP hrank A m hm e i⟩,
    datum_Ldeg_isLeast a ha X π hπ hbir hpoints hcriterion hminimal hDP hrank A m hm e⟩
  have h := S01.lsq_frobenius_datum 2 3 a ha hn X π hπ hbir hpoints hcriterion A m hm e
    hminimal hDP hrank
  change (ResolutionDatum.mk (sevenSurface a ha) X π hminimal hDP hrank).Lsq = 1 / 3
  rw [h]
  norm_num

end Existence

/-! ### Isolated: the completeness clause (lines 3186–3189, 3217–3260)

The union has no actual strict transforms `T_i` (vertical fibre through a centre), `Θ`
(diagonal), `Q_i`, `W_i` on `S_{3,3}`, so neither the realization of the other ten classes nor
the statement "exactly thirteen exterior negative prime curves / twenty-three negative prime
curves" is formalized. The arithmetic core of the completeness proof is the union's
`KltDP.EqualityContacts.admissible_iff_mem_patterns`; what the geometry must supply is that an
exterior negative prime curve `Z` has an admissible contact datum whose integral class is `[Z]`
(lines 3217–3241). This is recorded as an explicit hypothesis. -/

/-- The contact datum `(r, z_0, z_i, u_i, v_i)` attached to a class `x` in the lattice:
`r = (B+b)·x = 3L·x`, `z_0 = B·x`, `z_i = F_i·x`, `u_i = U_i·x`, `v_i = V_i·x`. -/
def contactOf (x : Vec) : KltDP.EqualityContacts.Contact :=
  let br : Fin 3 → KltDP.EqualityContacts.Branch := fun i =>
    ⟨(FrobeniusPicard.pairing (retainedVector 2 3 (.inr (.inl i))) x).toNat,
      (FrobeniusPicard.pairing (retainedVector 2 3 (.inr (.inr (i, 0)))) x).toNat,
      (FrobeniusPicard.pairing (retainedVector 2 3 (.inr (.inr (i, 1)))) x).toNat⟩
  ⟨(FrobeniusPicard.pairing Mvec x).toNat,
    (FrobeniusPicard.pairing (retainedVector 2 3 (.inl ())) x).toNat, br 0, br 1, br 2⟩

/-- The thirteen classes have the thirteen contact patterns of the union (lines 3290–3296). -/
theorem contactOf_thirteen :
    (∀ i, contactOf (Pvec i) = KltDP.EqualityContacts.P i) ∧
    (∀ i, contactOf (Tvec i) = KltDP.EqualityContacts.T i) ∧
    contactOf thetaVec = KltDP.EqualityContacts.theta ∧
    (∀ i, contactOf (Qvec i) = KltDP.EqualityContacts.Q i) ∧
    (∀ i, contactOf (Wvec i) = KltDP.EqualityContacts.W i) := by decide

/-- **Completeness, isolated** (lines 3217–3260). If every exterior negative prime curve `Z` of the
seven-point surface has nonnegative contacts with `D` and its contact datum is admissible (the two
identities of lines 3224–3228 and the integrality congruences of line 3241 — the geometric input
not available in the union), then its class in the lattice is one of the thirteen classes
`P_i, T_i, Θ, Q_i, W_i`. -/
theorem exterior_negative_class_mem_patterns_of (x : Vec)
    (hadm : (contactOf x).Admissible)
    (hx : x = ofClassVector (KltDP.Support.integralClass (contactOf x))) :
    x ∈ ({Pvec 0, Pvec 1, Pvec 2, Tvec 0, Tvec 1, Tvec 2, thetaVec, Qvec 0, Qvec 1, Qvec 2,
      Wvec 0, Wvec 1, Wvec 2} : Finset Vec) := by
  have hmem := (KltDP.EqualityContacts.admissible_iff_mem_patterns _).mp hadm
  rw [hx]
  simp only [KltDP.EqualityContacts.patterns, Finset.mem_insert, Finset.mem_singleton] at hmem
  obtain ⟨hP, hT, hth, hQ, hW⟩ := ofClassVector_patterns
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
    simp only [hP, hT, hth, hQ, hW, Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

end KltDP.Manuscript.S11

#print axioms KltDP.Manuscript.S11.thirteen_contacts
#print axioms KltDP.Manuscript.S11.newestCurveP_isMinusOne
#print axioms KltDP.Manuscript.S11.A_eq_submatrix
#print axioms KltDP.Manuscript.S11.sevenPointNegativeCurves
#print axioms KltDP.Manuscript.S11.exterior_negative_class_mem_patterns_of
