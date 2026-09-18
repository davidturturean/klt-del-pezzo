import KltDP.Geometry.KltResolutionNoetherRelation
import KltDP.Geometry.KltResolutionPicardRank
import KltDP.Geometry.KltMinimalResolutionAutomaticGeometry

/-! The easy canonical-square range of the actual seven-point bound.
The original exceptional forest and original Noether relation reduce every
possible counterexample to K²≤1 and Picard rank at least nine. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsMinimalResolution

open SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- The original singular points are no more numerous than the actual
exceptional primes; this uses the proved original component correspondence. -/
theorem singularPoints_card_le_exceptional_card
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X) :
    X.singularPoints.card ≤ Nat.card (ActualExceptionalIncidence.Vertices π) := by
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    hmin.toIsResolution.exceptionalCurves_finite_of_actualMap
  have hcount := (hmin.exceptional_forest_and_singular_count_from_klt hklt).2.1
  rw [hcount]
  exact Nat.card_le_card_of_surjective
    (ActualExceptionalIncidence.graph π).connectedComponentMk Quot.mk_surjective

variable (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
  (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 0 < p)

include hmin hDP hrank hp in
/-- The exact number of original exceptional primes in terms of the
square of any actual canonical representative. -/
theorem exceptional_card_eq_nine_sub_canonical_square
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2) :
    (Nat.card (ActualExceptionalIncidence.Vertices π) : ℤ) =
      9 - S.intersectionPairing hmin.regular K K := by
  have hklt : IsKlt X := by
    obtain ⟨KX, hKX, _⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
    exact ⟨KX, hKX⟩
  have hrho := hmin.picardRank_eq_of_klt hklt p hp
  rw [hrank] at hrho
  have hrhoZ : (S.picardRank : ℤ) =
      1 + (Nat.card (ActualExceptionalIncidence.Vertices π) : ℤ) := by
    exact_mod_cast hrho
  have hNoether := hmin.noetherRelation_of_kltDelPezzo hDP hrank p hp K eK
  change S.intersectionPairing hmin.regular K K + (S.picardRank : ℤ) = 10 at hNoether
  omega

include hmin hDP hrank hp in
/-- The original seven-point bound when the canonical square is at least two. -/
theorem singularPoints_card_le_seven_of_canonical_square_ge_two
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (hK : 2 ≤ S.intersectionPairing hmin.regular K K) :
    X.singularPoints.card ≤ 7 := by
  have hklt : IsKlt X := by
    obtain ⟨KX, hKX, _⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
    exact ⟨KX, hKX⟩
  have hs := hmin.singularPoints_card_le_exceptional_card hklt
  have hsZ : (X.singularPoints.card : ℤ) ≤
      (Nat.card (ActualExceptionalIncidence.Vertices π) : ℤ) := by exact_mod_cast hs
  have hcount := hmin.exceptional_card_eq_nine_sub_canonical_square hDP hrank p hp K eK
  omega

include hmin hDP hrank hp in
/-- Every possible original counterexample lies in the remaining
canonical-square range and has the required large Picard rank. -/
theorem counterexample_canonical_square_and_picardRank
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (hcounter : 7 < X.singularPoints.card) :
    S.intersectionPairing hmin.regular K K ≤ 1 ∧ 9 ≤ S.picardRank := by
  have hklt : IsKlt X := by
    obtain ⟨KX, hKX, _⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
    exact ⟨KX, hKX⟩
  have hs := hmin.singularPoints_card_le_exceptional_card hklt
  have hrho := hmin.picardRank_eq_of_klt hklt p hp
  rw [hrank] at hrho
  have hcount := hmin.exceptional_card_eq_nine_sub_canonical_square hDP hrank p hp K eK
  constructor <;> omega

end KltDP.Geometry.IsMinimalResolution

#print axioms KltDP.Geometry.IsMinimalResolution.singularPoints_card_le_seven_of_canonical_square_ge_two
#print axioms KltDP.Geometry.IsMinimalResolution.counterexample_canonical_square_and_picardRank
