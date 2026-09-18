import KltDP.Geometry.FrobeniusExactSingularCount
import KltDP.Geometry.FrobeniusTargetIntrinsicDelPezzoIff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual Frobenius singular-count consequences

The actual regular-target canonical-discrepancy theorem supplies the reverse
singularity inclusion. The original surface, contraction and branch curves
are retained. Compilation and literature acceptance are tracked separately.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusSharpness

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreSemiampleConstruction
open NormalProjectiveSurface

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

/-- Distinct centers in the original algebraically closed field. -/
private def centers (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) : Fin n → k :=
  fun i => Infinite.natEmbedding k i.val

private theorem centers_injective (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) :
    Function.Injective (centers k n) := by
  intro i j hij
  exact Fin.val_injective ((Infinite.natEmbedding k).injective hij)

-- Join the original exact-count construction with the intrinsic criterion
-- before selecting a characteristic. Only the arithmetic range is an input.
private theorem exists_rank_one_delPezzo_exact_count
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (hn : 2 < n) (hparameters : q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3)) :
    ∃ S : NormalProjectiveSurface k,
      S.NumericalSpaceFiniteDimensional ∧ S.picardRank = 1 ∧ IsKltDelPezzo S ∧
        S.singularPoints.card = 2 * n + 1 ∧ S.singularPointCount = 2 * n + 1 := by
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
  refine ⟨S, hdim, hrank, ?_, hcard, hcount⟩
  exact (target_isKltDelPezzo_iff_parameters
    q n a ha hn S π hπ hbir hpoints hcriterion A m hm e hA).mpr hparameters

/-- Over every algebraically closed characteristic-three field, the actual
n=3 construction gives a rank-one klt del Pezzo surface with exactly seven
distinct singular points. -/
theorem exists_rank_one_klt_delPezzo_seven_singular_points_char_three
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k 3] :
    ∃ S : NormalProjectiveSurface k,
      S.NumericalSpaceFiniteDimensional ∧ S.picardRank = 1 ∧ IsKltDelPezzo S ∧
        S.singularPoints.card = 7 ∧ S.singularPointCount = 7 := by
  letI : Fact (Nat.Prime (2 + 1)) := ⟨Nat.prime_three⟩
  obtain ⟨S, hdim, hrank, hdelPezzo, hcard, hcount⟩ :=
    exists_rank_one_delPezzo_exact_count (k := k) 2 3 (by decide)
      (Or.inr ⟨rfl, rfl⟩)
  exact ⟨S, hdim, hrank, hdelPezzo, hcard, hcount⟩

/-- Over every algebraically closed characteristic-two field, the actual
n=N+3 construction gives a rank-one klt del Pezzo surface with more than N
distinct singular points; its exact count is retained. -/
theorem exists_rank_one_klt_delPezzo_more_than_char_two
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2] (N : ℕ) :
    ∃ S : NormalProjectiveSurface k,
      S.NumericalSpaceFiniteDimensional ∧ S.picardRank = 1 ∧ IsKltDelPezzo S ∧
        S.singularPoints.card = 2 * (N + 3) + 1 ∧
        S.singularPointCount = 2 * (N + 3) + 1 ∧ N < S.singularPointCount := by
  letI : Fact (Nat.Prime (1 + 1)) := ⟨Nat.prime_two⟩
  obtain ⟨S, hdim, hrank, hdelPezzo, hcard, hcount⟩ :=
    exists_rank_one_delPezzo_exact_count (k := k) 1 (N + 3) (by omega) (Or.inl rfl)
  refine ⟨S, hdim, hrank, hdelPezzo, hcard, hcount, ?_⟩
  rw [hcount]
  omega

end KltDP.Geometry.FrobeniusSharpness

#print axioms KltDP.Geometry.FrobeniusSharpness.exists_rank_one_klt_delPezzo_seven_singular_points_char_three
#print axioms KltDP.Geometry.FrobeniusSharpness.exists_rank_one_klt_delPezzo_more_than_char_two
