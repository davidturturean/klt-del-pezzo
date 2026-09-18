import KltDP.Manuscript.S11.NegativeCurves
import KltDP.Geometry.SmoothCanonicalCartierRepresentative
import KltDP.Geometry.SmoothCanonicalExteriorComparison

/-!
# Proposition 11.2 (`prop:equality-adjoints`, manuscript lines 3263–3335):
# adjoint identities and singular-point counts on the equality example

Formalized here, on the seven-point surface `S = S_{3,3}` of `S11/NegativeCurves`:

* the five adjoint identities of lines 3268–3274 as identities in the Picard lattice
  `ℤ¹¹ = ⟨a, b, E_{ij}⟩` (`adjoint_vector_identities`), and as identities in `Pic(S)` between
  the Picard classes of the *actual* divisors `K_S, B, F_i, U_i, V_i, P_i` on the left and the
  lattice classes of `T_i, Θ, Q_i, W_i` on the right (`adjoint_one`, …, `adjoint_five`; the
  version with the datum's own canonical divisor `R.KS` is `datum_KS_class` + these);
* the degree bookkeeping of the adjoint pairs `P_i ↔ T_i` (`3 L · T_i = 3 L · P_i = 1`);
* the numerical content of the one-component replacement at `P_i` (lines 3309–3322): after
  deleting `V_i` and contracting `P_i` the images `B + P_i`, `F_i + P_i` form an `A₂` block,
  `U_i` becomes an isolated `A₁`, the two other `A₂` blocks and the two other `[3]` curves are
  unchanged, and `L_i^† = -K_S + P_i - (F_j + F_k)/3` is orthogonal to all nine retained
  classes and has square `2/3` (`replacement_numerics`).

Not formalized (isolated): the linear equivalences as equalities of *actual* divisors on the
right-hand sides (the curves `T_i, Θ, Q_i, W_i` are not constructed in the union, see
`S11/NegativeCurves`), the uniqueness of the effective representatives (lines 3301–3304), and
the one-component replacement theorem itself (`thm:one-component-replacement`, §4, not yet
formalized), hence the six-point target of lines 3283–3286.
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
open KltDP.Examples.FrobeniusMultiCentrePicardRealization
open KltDP.Geometry.PrimeCurveClassPairing
open KltDP.Geometry.InvertibleSheafSectionPowers
open KltDP.Manuscript KltDP.Manuscript.S10

universe u

namespace KltDP.Manuscript.S11

/-! ### The retained classes and the identities in the lattice -/

/-- `B = 3a + b - Σ E_{ij}`. -/
abbrev Bvec : Vec := retainedVector 2 3 (.inl ())
/-- `F_i = b - Σ_j E_{ij}`. -/
abbrev Fvec (i : Fin 3) : Vec := retainedVector 2 3 (.inr (.inl i))
/-- `U_i = C_{i1} = E_{i1} - E_{i2}`. -/
abbrev Uvec (i : Fin 3) : Vec := retainedVector 2 3 (.inr (.inr (i, 0)))
/-- `V_i = C_{i2} = E_{i2} - E_{i3}`. -/
abbrev Vvec (i : Fin 3) : Vec := retainedVector 2 3 (.inr (.inr (i, 1)))

/-- **The five adjoint identities** (lines 3268–3274) in the lattice `⟨a, b, E_{ij}⟩`, for
`{i, j, k} = {0, 1, 2}`:
`K + V_i + B + F_i + 2P_i = T_i`, `K + U_i + F_j + F_k + 2T_i = P_i`,
`K + Σ U_i + 2Θ = Σ P_i`, `K + U_i + V_j + V_k + 2Q_i = P_i + T_j + T_k`,
`K + U_j + V_j + W_i = P_k + T_k`. -/
theorem adjoint_vector_identities :
    (∀ i : Fin 3, Kvec + Vvec i + Bvec + Fvec i + 2 • Pvec i = Tvec i) ∧
    (∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      Kvec + Uvec i + Fvec j + Fvec k + 2 • Tvec i = Pvec i) ∧
    (Kvec + (Uvec 0 + Uvec 1 + Uvec 2) + 2 • thetaVec = Pvec 0 + Pvec 1 + Pvec 2) ∧
    (∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      Kvec + Uvec i + Vvec j + Vvec k + 2 • Qvec i = Pvec i + Tvec j + Tvec k) ∧
    (∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
      Kvec + Uvec j + Vvec j + Wvec i = Pvec k + Tvec k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- "Each right side consists of pairwise disjoint `(-1)`-curves" (line 3301): the classes on
the right-hand sides are orthogonal: `P_i · P_j = P_i · T_j = T_i · T_j = 0` (`i ≠ j`),
`P_k · T_k = 0`. -/
theorem right_hand_sides_orthogonal :
    (∀ i j : Fin 3, i ≠ j → FrobeniusPicard.pairing (Pvec i) (Pvec j) = 0) ∧
    (∀ i j : Fin 3, i ≠ j → FrobeniusPicard.pairing (Pvec i) (Tvec j) = 0) ∧
    (∀ i j : Fin 3, i ≠ j → FrobeniusPicard.pairing (Tvec i) (Tvec j) = 0) ∧
    (∀ k : Fin 3, FrobeniusPicard.pairing (Pvec k) (Tvec k) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The adjoint pairs `P_i ↔ T_i` preserve the `L`-degree: `3L · P_i = 3L · T_i = 1`
(line 3277–3278). -/
theorem adjoint_pairs_degree (i : Fin 3) :
    FrobeniusPicard.pairing Mvec (Pvec i) = FrobeniusPicard.pairing Mvec (Tvec i) := by
  rw [thirteen_degrees.1 i, thirteen_degrees.2.1 i]

/-! ### The identities in `Pic(S)` for the actual divisors -/

section Geometry

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 3]

local instance factPrimeThreeA : Fact (2 + 1).Prime := ⟨Nat.prime_three⟩

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

variable (a : Fin 3 → k) (ha : Function.Injective a)

/-- The class in `Pic(S)` realizing a lattice vector (the union's `realization`, typed on the
seven-point surface). -/
abbrev latticeClass (x : Vec) : Additive (sevenSurface a ha).toScheme.Pic := realization 2 3 a x

/-- The prime Cartier divisor of a retained curve. -/
abbrev retainedDiv (l : RetainedLabel 2 3) : CartierDivisor (sevenSurface a ha).toScheme :=
  (sevenSurface a ha).primeCurveCartier (sevenRegular a ha) (retainedCurve 2 3 a ha l)

/-- The prime Cartier divisor of `P_i`. -/
abbrev newestDiv (i : Fin 3) : CartierDivisor (sevenSurface a ha).toScheme :=
  (sevenSurface a ha).primeCurveCartier (sevenRegular a ha) (newestCurveP 2 3 a ha i)

/-- `B`, `F_i`, `U_i`, `V_i` as actual Cartier divisors. -/
abbrev Bdiv : CartierDivisor (sevenSurface a ha).toScheme := retainedDiv a ha (.inl ())
abbrev Fdiv (i : Fin 3) : CartierDivisor (sevenSurface a ha).toScheme := retainedDiv a ha (.inr (.inl i))
abbrev Udiv (i : Fin 3) : CartierDivisor (sevenSurface a ha).toScheme :=
  retainedDiv a ha (.inr (.inr (i, 0)))
abbrev Vdiv (i : Fin 3) : CartierDivisor (sevenSurface a ha).toScheme :=
  retainedDiv a ha (.inr (.inr (i, 1)))

theorem retainedDiv_class (l : RetainedLabel 2 3) :
    cartierPicardHom (sevenSurface a ha).toScheme (retainedDiv a ha l) =
      latticeClass a ha (retainedVector 2 3 l) :=
  retainedCurve_class a ha l

omit [CharP k 3] in
theorem newestDiv_class (i : Fin 3) :
    cartierPicardHom (sevenSurface a ha).toScheme (newestDiv a ha i) = latticeClass a ha (Pvec i) :=
  newestCurveP_class a ha i

theorem Kdiv_class' :
    cartierPicardHom (sevenSurface a ha).toScheme (Kdiv a ha) = latticeClass a ha Kvec :=
  Kdiv_class a ha

/-- **Identity 1**: `K_S + V_i + B + F_i + 2P_i` has the class `T_i = a - E_{i1}` (line 3269). -/
theorem adjoint_one (i : Fin 3) :
    cartierPicardHom (sevenSurface a ha).toScheme
        (Kdiv a ha + Vdiv a ha i + Bdiv a ha + Fdiv a ha i + 2 • newestDiv a ha i) =
      latticeClass a ha (Tvec i) := by
  have h := congrArg (latticeClass a ha) (adjoint_vector_identities.1 i)
  simp only [latticeClass, map_add, map_nsmul] at h
  simpa only [map_add, map_nsmul, Kdiv_class', retainedDiv_class, newestDiv_class, latticeClass]
    using h

/-- **Identity 2**: `K_S + U_i + F_j + F_k + 2T_i ∼ P_i` (line 3270), with `T_i` as a class. -/
theorem adjoint_two (i j l : Fin 3) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    cartierPicardHom (sevenSurface a ha).toScheme
        (Kdiv a ha + Udiv a ha i + Fdiv a ha j + Fdiv a ha l) + 2 • latticeClass a ha (Tvec i) =
      cartierPicardHom (sevenSurface a ha).toScheme (newestDiv a ha i) := by
  have h := congrArg (latticeClass a ha) (adjoint_vector_identities.2.1 i j l hij hjl hil)
  simp only [latticeClass, map_add, map_nsmul] at h
  simpa only [map_add, map_nsmul, Kdiv_class', retainedDiv_class, newestDiv_class, latticeClass]
    using h

/-- **Identity 3**: `K_S + Σ U_i + 2Θ ∼ Σ P_i` (line 3271), with `Θ` as a class. -/
theorem adjoint_three :
    cartierPicardHom (sevenSurface a ha).toScheme
        (Kdiv a ha + (Udiv a ha 0 + Udiv a ha 1 + Udiv a ha 2)) + 2 • latticeClass a ha thetaVec =
      cartierPicardHom (sevenSurface a ha).toScheme
        (newestDiv a ha 0 + newestDiv a ha 1 + newestDiv a ha 2) := by
  have h := congrArg (latticeClass a ha) adjoint_vector_identities.2.2.1
  simp only [latticeClass, map_add, map_nsmul] at h
  simpa only [map_add, map_nsmul, Kdiv_class', retainedDiv_class, newestDiv_class, latticeClass]
    using h

/-- **Identity 4**: `K_S + U_i + V_j + V_k + 2Q_i ∼ P_i + T_j + T_k` (line 3272). -/
theorem adjoint_four (i j l : Fin 3) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    cartierPicardHom (sevenSurface a ha).toScheme
        (Kdiv a ha + Udiv a ha i + Vdiv a ha j + Vdiv a ha l) + 2 • latticeClass a ha (Qvec i) =
      cartierPicardHom (sevenSurface a ha).toScheme (newestDiv a ha i) +
        latticeClass a ha (Tvec j) + latticeClass a ha (Tvec l) := by
  have h := congrArg (latticeClass a ha) (adjoint_vector_identities.2.2.2.1 i j l hij hjl hil)
  simp only [latticeClass, map_add, map_nsmul] at h
  simpa only [map_add, map_nsmul, Kdiv_class', retainedDiv_class, newestDiv_class, latticeClass]
    using h

/-- **Identity 5**: `K_S + U_j + V_j + W_i ∼ P_k + T_k` (`j ≠ i`, line 3273). -/
theorem adjoint_five (i j l : Fin 3) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    cartierPicardHom (sevenSurface a ha).toScheme (Kdiv a ha + Udiv a ha j + Vdiv a ha j) +
        latticeClass a ha (Wvec i) =
      cartierPicardHom (sevenSurface a ha).toScheme (newestDiv a ha l) + latticeClass a ha (Tvec l) := by
  have h := congrArg (latticeClass a ha) (adjoint_vector_identities.2.2.2.2 i j l hij hjl hil)
  simp only [latticeClass, map_add, map_nsmul] at h
  simpa only [map_add, map_nsmul, Kdiv_class', retainedDiv_class, newestDiv_class, latticeClass]
    using h

/-! ### The datum's canonical divisor -/

variable (Y : NormalProjectiveSurface k) (π : (sevenSurface a ha).toScheme ⟶ Y.toScheme)
    (hmin : IsMinimalResolution (sevenSurface a ha) Y π) (hDP : IsKltDelPezzo Y)
    (hrank : Y.picardRank = 1)

/-- The datum's chosen canonical Cartier divisor `K_S` and the union's `canonicalCartier` have
the same Picard class (both represent the canonical sheaf): `[K_S] = -2a - 2b + Σ E_{ij}`. -/
theorem datum_KS_class :
    cartierPicardHom (sevenSurface a ha).toScheme (datum a ha Y π hmin hDP hrank).KS =
      latticeClass a ha Kvec := by
  letI : IsSmoothOfRelativeDimension 2 (sevenSurface a ha).structureMorphism :=
    multiStructure_smoothTwo (2 + 1) 3 a ha
  have eD : cartierDivisorModule (sevenSurface a ha).toScheme (datum a ha Y π hmin hDP hrank).KS ≅
      (SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface
        (sevenSurface a ha).structureMorphism).obj :=
    (datum a ha Y π hmin hDP hrank).eKS ≪≫
      (SmoothCanonicalExteriorComparison.canonicalSheafOfSmoothSurfaceIsoExterior
        (sevenSurface a ha).structureMorphism).symm
  have eE : cartierDivisorModule (sevenSurface a ha).toScheme (Kdiv a ha) ≅
      (SmoothSurfaceKaehlerAtlas.canonicalSheafOfSmoothSurface
        (sevenSurface a ha).structureMorphism).obj :=
    canonicalCartierIso 2 3 a ha (sevenProj a)
  have hlin := SmoothCanonicalCartierRepresentative.choices_linearlyEquivalent (sevenSurface a ha)
    (datum a ha Y π hmin hDP hrank).KS (Kdiv a ha) eD eE
  have hcls := ((sevenSurface a ha).linearlyEquivalent_iff_weilClassMap_eq _ _).mp hlin
  have h1 := (sevenSurface a ha).regularWeilClassPicardEquiv_of_cartier (sevenRegular a ha)
    (datum a ha Y π hmin hDP hrank).KS
  have h2 := (sevenSurface a ha).regularWeilClassPicardEquiv_of_cartier (sevenRegular a ha)
    (Kdiv a ha)
  rw [hcls, h2] at h1
  rw [← Kdiv_class' a ha]
  change Additive.ofMul (cartierPicardClass (sevenSurface a ha).toScheme
      (datum a ha Y π hmin hDP hrank).KS) =
    Additive.ofMul (cartierPicardClass (sevenSurface a ha).toScheme (Kdiv a ha))
  rw [h1]

end Geometry

/-! ### The numerical content of the one-component replacement at `P_i` (lines 3309–3322) -/

/-- The nine retained classes after deleting `V_i` and contracting `P_i`: the images of `B` and
`F_i` acquire the class of `P_i` (`B + P_i`, `F_i + P_i`), all others are unchanged. -/
def replacedVector (i : Fin 3) (l : RetainedLabel 2 3) : Vec :=
  match l with
  | .inl _ => Bvec + Pvec i
  | .inr (.inl i') => if i' = i then Fvec i + Pvec i else Fvec i'
  | .inr (.inr (i', j)) => retainedVector 2 3 (.inr (.inr (i', j)))

/-- `3 L_i^† = -3K_S + 3P_i - F_j - F_k` (line 3318, cleared of the denominator). -/
def replacedNef (i : Fin 3) : Vec :=
  -(3 • Kvec) + 3 • Pvec i - ∑ j ∈ Finset.univ.erase i, Fvec j

/-- **Numerical content of the replacement at `P_i`** (lines 3309–3322): the images of `B` and
`F_i` are `(-2)`-classes meeting once (one `A₂` block), `U_i` is a `(-2)`-class orthogonal to both
(an isolated `A₁`), the other two clusters and the other two `F`'s are untouched and orthogonal to
the new block; `L_i^†` is orthogonal to all nine retained classes and `(L_i^†)² = 2/3`
(`(3L_i^†)² = 6`). -/
theorem replacement_numerics (i : Fin 3) :
    FrobeniusPicard.pairing (Bvec + Pvec i) (Bvec + Pvec i) = -2 ∧
    FrobeniusPicard.pairing (Fvec i + Pvec i) (Fvec i + Pvec i) = -2 ∧
    FrobeniusPicard.pairing (Bvec + Pvec i) (Fvec i + Pvec i) = 1 ∧
    FrobeniusPicard.pairing (Uvec i) (Bvec + Pvec i) = 0 ∧
    FrobeniusPicard.pairing (Uvec i) (Fvec i + Pvec i) = 0 ∧
    FrobeniusPicard.pairing (Uvec i) (Uvec i) = -2 ∧
    (∀ j : Fin 3, j ≠ i → FrobeniusPicard.pairing (Fvec j) (Bvec + Pvec i) = 0 ∧
      FrobeniusPicard.pairing (Fvec j) (Fvec i + Pvec i) = 0 ∧
      FrobeniusPicard.pairing (Uvec j) (Bvec + Pvec i) = 0 ∧
      FrobeniusPicard.pairing (Uvec j) (Fvec i + Pvec i) = 0 ∧
      FrobeniusPicard.pairing (Vvec j) (Bvec + Pvec i) = 0 ∧
      FrobeniusPicard.pairing (Vvec j) (Fvec i + Pvec i) = 0) ∧
    (∀ l : RetainedLabel 2 3, l ≠ .inr (.inr (i, 1)) →
      FrobeniusPicard.pairing (replacedNef i) (replacedVector i l) = 0) ∧
    FrobeniusPicard.pairing (replacedNef i) (replacedNef i) = 6 := by
  fin_cases i <;> decide

/-- `(L_i^†)² = 2/3` (line 3320). -/
theorem replacedNef_square (i : Fin 3) :
    ((FrobeniusPicard.pairing (replacedNef i) (replacedNef i) : ℤ) : ℚ) / 9 = 2 / 3 := by
  rw [(replacement_numerics i).2.2.2.2.2.2.2.2]
  norm_num

/-- The component count drops from seven to six: `4 + 3 = 7` blocks before (four `[3]`, three
`A₂`), `2 + 3 + 1 = 6` after (two `[3]`, three `A₂`, one `A₁`), i.e. the change `1 - 2 = -1` of
line 3283 (`s_{V_i} - 2 = -1`, line 3322). -/
theorem component_count_change : (4 + 3 : ℕ) = 7 ∧ (2 + 3 + 1 : ℕ) = 6 ∧ (7 : ℤ) - 1 = 6 := by
  norm_num

end KltDP.Manuscript.S11

#print axioms KltDP.Manuscript.S11.adjoint_vector_identities
#print axioms KltDP.Manuscript.S11.adjoint_one
#print axioms KltDP.Manuscript.S11.adjoint_five
#print axioms KltDP.Manuscript.S11.datum_KS_class
#print axioms KltDP.Manuscript.S11.replacement_numerics
