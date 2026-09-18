import KltDP.Manuscript.Datum.AnticanonicalClass
import KltDP.Geometry.FrobeniusExactSingularCount
import KltDP.Geometry.FrobeniusTargetIntrinsicDelPezzoIff
import KltDP.Geometry.FrobeniusTargetIsCanonical
import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceKlt
import KltDP.Examples.FrobeniusTargetCanonicalPullbackClass
import KltDP.Geometry.CanonicalWeilClassIndependent
import KltDP.Geometry.QCartierPullbackPrincipal
import KltDP.Geometry.RegularSurfaceWeilPicard
import KltDP.Geometry.NumericalEquivalence
import KltDP.Geometry.NefNullCurveNegativeSquare
import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Theorem 1.2 (`thm:examples`, manuscript lines 121–130): the Frobenius examples

Manuscript `source/manuscript.tex`, Theorem 1.2 (Bernasconi; Keel–McKernan) and
its proof (lines 3121–3130), which specialises Proposition 10.1
(`prop:frobenius-family`, lines 2892–2933) to `(p,n) = (3,3)` and to `p = 2`.

The singular-point counts, the Picard rank and the klt del Pezzo property of the
contracted Frobenius surfaces are already in the union
(`exists_normal_projective_surface_rank_one_klt_exact_singular_count`,
`target_isKltDelPezzo_iff_parameters`). The new content here is the value of
`K_X² = L²`, represented as `R.Lsq` for a resolution datum `R` whose resolution
surface is the multi-centre Frobenius source `S_{p,n}` and whose `π` is the
original contraction. The manuscript formula (Proposition 10.1)
`L ∼_ℚ t_{p,n} M`, `M² = p(n-2)`, `L² = d_{p,n}²/(p(n-2))` with
`d_{p,n} = 2 - (p-2)(n-2)` is assembled from the union's
`target_canonical_pullback_class` (the class of `π^*K_X` on the source) and
`contractingDivisor_square` (`M² = p(n-2)`).
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
open KltDP.Geometry.InvertibleSheafSectionPowers

universe u

namespace KltDP.Manuscript.S01

open KltDP.Manuscript

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

/-! ### Two general facts about a resolution datum -/

/-- The numerical class of (the rationalisation of) the Weil divisor of an actual Cartier
divisor is its Cartier numerical class `cartierClass`. -/
theorem rationalWeilNumericalMap_rationalize_cartierToWeilHom
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hreg : ∀ x : X.Point, RegularPoint X.toScheme x) (D : CartierDivisor X.toScheme) :
    X.rationalWeilNumericalMap hreg (rationalizeWeilDivisor X (X.cartierToWeilHom D)) =
      NefNullCurveNegativeSquare.cartierClass X D := by
  rw [← X.picardNumericalMap_regularWeilPicardClass hreg]
  have h2 : X.regularWeilClassPicardEquiv hreg (X.weilClassMap (X.cartierToWeilHom D)) =
      Additive.ofMul (cartierPicardClass X.toScheme D) := by
    rw [← X.regularWeilClassPicardEquiv_of_cartier hreg D, ofMul_toMul]
  have h : Additive.ofMul (X.regularWeilPicardClass hreg (X.cartierToWeilHom D)) =
      cartierPicardHom X.toScheme D := by
    change Additive.ofMul (X.regularWeilClassPicardEquiv hreg
      (X.weilClassMap (X.cartierToWeilHom D))).toMul = _
    rw [ofMul_toMul, h2]
    rfl
  rw [h]
  rfl

/-- **`L² = c² · M²` whenever `π^*K_X ∼_ℚ c·M`** for an actual Cartier divisor `M` on the
resolution surface: the manuscript's `L = π^*(-K_X) ∼_ℚ t M ⇒ L² = t² M²`
(Proposition 10.1, lines 2911–2916). -/
theorem lsq_of_class_eq {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)
    (M : CartierDivisor R.S.toScheme) (c : ℚ)
    (h : R.S.rationalWeilClassMap R.pullbackKX =
      c • R.S.rationalWeilClassMap (rationalizeWeilDivisor R.S (R.S.cartierToWeilHom M))) :
    R.Lsq = c ^ 2 * (R.S.intersectionPairing R.hreg M M : ℚ) := by
  have hnum : R.S.rationalWeilNumericalMap R.hreg R.pullbackKX =
      c • NefNullCurveNegativeSquare.cartierClass R.S M := by
    have h' := congrArg (R.S.rationalWeilClassNumericalMap R.hreg) h
    rw [map_smul, R.S.rationalWeilClassNumericalMap_class R.hreg,
      R.S.rationalWeilClassNumericalMap_class R.hreg,
      rationalWeilNumericalMap_rationalize_cartierToWeilHom R.S R.hreg M] at h'
    exact h'
  have hL : R.Lnum = (-c) • NefNullCurveNegativeSquare.cartierClass R.S M := by
    change R.S.rationalWeilNumericalMap R.hreg (-R.pullbackKX) = _
    rw [map_neg, hnum, neg_smul]
  change R.S.numericalIntersectionBilinForm R.hreg R.Lnum R.Lnum = _
  rw [hL, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    NefNullCurveNegativeSquare.cartierClass_pairing]
  ring

/-! ### `K_X²` of the contracted Frobenius surface `X_{p,n}` -/

section Frobenius

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme)
    [hproper : IsProper π] [hsurj : Surjective π] [hc : IsIso π.c]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0)
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj)

include hn hproper hsurj hc hπ hbir hconnected hcriterion hm e

/-- Proposition 10.1 (lines 2911–2916): for the resolution datum built from the original
Frobenius contraction `π : S_{p,n} → X_{p,n}`, `L² = d_{p,n}² / (p (n-2))`. -/
theorem lsq_frobenius_datum
    (hmin : IsMinimalResolution
      (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) Y π)
    (hDP : IsKltDelPezzo Y) (hrank : Y.picardRank = 1) :
    (ResolutionDatum.mk (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
        Y π hmin hDP hrank).Lsq =
      (2 - (((q + 1 : ℕ) : ℚ) - 2) * ((n : ℚ) - 2)) ^ 2 /
        (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2)) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  set R : ResolutionDatum k := ResolutionDatum.mk
    (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    Y π hmin hDP hrank with hR
  let K0 : Y.WeilDivisor := targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion
  have hK0canon : IsCanonicalWeilDivisor Y K0 :=
    targetCanonicalWeil_isCanonical q n a ha hn Y π hπ hbir hconnected hcriterion
  have hK0qc : Y.QCartier (rationalizeWeilDivisor Y K0) :=
    (targetCanonicalWeil_isKltWithCanonicalDivisor q n a ha hn Y π hπ hbir hconnected
      hcriterion A m hm e).2.1
  -- the chosen canonical divisor of the datum is linearly equivalent to the constructed one
  have hlin : Y.LinearlyEquivalent R.KX K0 :=
    IsCanonicalWeilDivisor.linearlyEquivalent R.KX_klt.1 hK0canon
  have hclass1 : R.S.rationalWeilClassMap R.pullbackKX =
      (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilClassMap
        (QCartierPullback.pullback
          (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
          (Y := Y) π (rationalizeWeilDivisor Y K0) hK0qc) :=
    ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).rationalWeilClassMap_eq_iff
      _ _).mpr
      (QCartierPullback.pullback_qLinearlyEquivalent
        (X := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
        (Y := Y) π _ _ R.KX_qCartier hK0qc (Y.qLinearlyEquivalent_of_linearlyEquivalent hlin))
  have hclass2 := FrobeniusTargetCanonicalPullbackClass.target_canonical_pullback_class
    q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e hK0qc
  dsimp only at hclass2
  have hsq := lsq_of_class_eq R
    (contractingDivisor q n a ha (originalMultiStructureProjective k (q + 1) n a)) _
    (hclass1.trans hclass2)
  have hM2 : R.S.intersectionPairing R.hreg
      (contractingDivisor q n a ha (originalMultiStructureProjective k (q + 1) n a))
      (contractingDivisor q n a ha (originalMultiStructureProjective k (q + 1) n a)) =
      ((q + 1 : ℕ) : ℤ) * ((n : ℤ) - 2) :=
    contractingDivisor_square q n a ha (originalMultiStructureProjective k (q + 1) n a)
  rw [hsq, hM2]
  have hp0 : ((q + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero q)
  have hr0 : ((n : ℚ) - 2) ≠ 0 := by
    have h2n : (2 : ℚ) < n := by exact_mod_cast hn
    exact ne_of_gt (sub_pos.mpr h2n)
  push_cast at hp0 hr0 ⊢
  field_simp
  ring

end Frobenius

/-! ### The examples -/

/-- Distinct centres in the algebraically closed (hence infinite) field. -/
private def centers (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) : Fin n → k :=
  fun i => Infinite.natEmbedding k i.val

private theorem centers_injective (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    Function.Injective (centers k n) := by
  intro i j hij
  exact Fin.val_injective ((Infinite.natEmbedding k).injective hij)

/-- The common core: for `p = q + 1` prime, `n > 2` and the parameters in the ample range,
the contracted Frobenius surface `X_{p,n}` is a rank-one klt del Pezzo surface with `2n+1`
singular points and `K² = d_{p,n}²/(p(n-2))`, witnessed by the datum of its original
contraction. -/
theorem exists_frobenius_example
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (hn : 2 < n) (hparameters : q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3)) :
    ∃ X : NormalProjectiveSurface k, IsKltDelPezzo X ∧ X.picardRank = 1 ∧
      X.singularPoints.card = 2 * n + 1 ∧
      ∃ R : ResolutionDatum k, R.X = X ∧
        R.Lsq = (2 - (((q + 1 : ℕ) : ℚ) - 2) * ((n : ℚ) - 2)) ^ 2 /
          (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2)) := by
  let a : Fin n → k := centers k n
  have ha : Function.Injective a := centers_injective k n
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
      hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal,
      hKlt, hIsKlt, hsing, hcard, hcount⟩ :=
    exists_normal_projective_surface_rank_one_klt_exact_singular_count q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  have hDP : IsKltDelPezzo S :=
    (target_isKltDelPezzo_iff_parameters
      q n a ha hn S π hπ hbir hpoints hcriterion A m hm e hA).mpr hparameters
  refine ⟨S, hDP, hrank, hcard, ResolutionDatum.mk _ S π hminimal hDP hrank, rfl, ?_⟩
  exact lsq_frobenius_datum q n a ha hn S π hπ hbir hpoints hcriterion A m hm e
    hminimal hDP hrank

/-- **Theorem 1.2, characteristic three** (manuscript lines 121–124, proof lines 3121–3130):
over every algebraically closed field of characteristic three there is a klt del Pezzo
surface `X` with `ρ(X) = 1`, `n(X) = 7` and `K_X² = 1/3`; the square is `R.Lsq = L²`
for a resolution datum `R` of `X`. -/
theorem sharpnessExampleCharThree (k : Type u) [Field k] [IsAlgClosed k] [CharP k 3] :
    ∃ X : NormalProjectiveSurface k, IsKltDelPezzo X ∧ X.picardRank = 1 ∧
      X.singularPoints.card = 7 ∧
      ∃ R : ResolutionDatum k, R.X = X ∧ R.Lsq = 1 / 3 := by
  letI : Fact (Nat.Prime (2 + 1)) := ⟨Nat.prime_three⟩
  obtain ⟨X, hDP, hrank, hcard, R, hRX, hLsq⟩ :=
    exists_frobenius_example (k := k) 2 3 (by decide) (Or.inr ⟨rfl, rfl⟩)
  refine ⟨X, hDP, hrank, hcard, R, hRX, ?_⟩
  rw [hLsq]
  norm_num

/-- **Theorem 1.2, characteristic two** (manuscript lines 125–129, proof lines 3121–3130):
over every algebraically closed field of characteristic two and for every `n ≥ 3` there is
a klt del Pezzo surface `X_{2,n}` with `ρ = 1`, `n(X_{2,n}) = 2n+1` and
`K² = 2/(n-2)`; the square is `R.Lsq = L²` for a resolution datum `R` of `X_{2,n}`. -/
theorem characteristicTwoFamily (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
    (n : ℕ) (hn : 3 ≤ n) :
    ∃ X : NormalProjectiveSurface k, IsKltDelPezzo X ∧ X.picardRank = 1 ∧
      X.singularPoints.card = 2 * n + 1 ∧
      ∃ R : ResolutionDatum k, R.X = X ∧ R.Lsq = 2 / ((n : ℚ) - 2) := by
  letI : Fact (Nat.Prime (1 + 1)) := ⟨Nat.prime_two⟩
  obtain ⟨X, hDP, hrank, hcard, R, hRX, hLsq⟩ :=
    exists_frobenius_example (k := k) 1 n (by omega) (Or.inl rfl)
  refine ⟨X, hDP, hrank, hcard, R, hRX, ?_⟩
  rw [hLsq]
  have hr0 : ((n : ℚ) - 2) ≠ 0 := by
    have h3n : (3 : ℚ) ≤ n := by exact_mod_cast hn
    exact ne_of_gt (by linarith)
  push_cast
  field_simp
  ring

end KltDP.Manuscript.S01

#print axioms KltDP.Manuscript.S01.sharpnessExampleCharThree
#print axioms KltDP.Manuscript.S01.characteristicTwoFamily
