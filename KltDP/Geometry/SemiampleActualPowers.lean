import KltDP.Geometry.FiniteSectionTuples
import KltDP.Geometry.InvertibleSheafSectionPowers

/-!
# Semiampleness supplies sections of an actual tensor power

The Picard-power witness in the original semiampleness predicate is
isomorphic to the recursively constructed tensor power. Transporting the
free epimorphism supplies global generation of that actual power. On a
quasi-compact scheme its original sections give finite projective coordinates.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SemiampleActualPowers

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowers InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- The original Picard-power definition is equivalent to generation of
one positive recursively constructed actual tensor power. -/
theorem isSemiample_iff_power_globallyGenerated :
    Positivity.IsSemiample L ↔
      ∃ m : ℕ, 0 < m ∧ Positivity.IsGloballyGenerated (power L m).obj := by
  constructor
  · rintro ⟨m, hm, M, hM, hG⟩
    letI := Scheme.Modules.monoidalCategory X
    have hclass : M.toPic = (power L m).toPic := hM.trans (power_toPic L m).symm
    have hsk : toSkeleton M.obj = toSkeleton (power L m).obj := by
      have h := congrArg (fun p : X.Pic => (p : Skeleton X.Modules)) hclass
      simpa only [InvertibleSheaf.toPic_val] using h
    obtain ⟨e⟩ := (show Nonempty (M.obj ≅ (power L m).obj) from Quotient.exact hsk)
    exact ⟨m, hm, AmpleSerre.isGloballyGenerated_of_iso e hG⟩
  · rintro ⟨m, hm, hG⟩
    exact ⟨m, hm, power L m, power_toPic L m, hG⟩

/-- Finite original sections of an actual positive tensor power cover the
whole quasi-compact scheme and can be used as projective coordinates. -/
theorem exists_actual_power_tuple
    (hX : IsCompact (Set.univ : Set X)) (hL : Positivity.IsSemiample L) :
    ∃ (m : ℕ), 0 < m ∧ ∃ (n : ℕ) (s : Fin (n + 1) → (power L m).obj.sections),
      (⨆ i, nonvanishingOpen X (power L m) (s i)) = ⊤ := by
  obtain ⟨m, hm, hG⟩ := (isSemiample_iff_power_globallyGenerated L).mp hL
  obtain ⟨n, s, hs⟩ := FiniteSectionTuples.exists_tuple_of_globallyGenerated (power L m) hX hG
  exact ⟨m, hm, n, s, hs⟩

end KltDP.Geometry.SemiampleActualPowers
