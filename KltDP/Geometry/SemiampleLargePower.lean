import KltDP.Geometry.SemiampleActualPowers
import KltDP.Geometry.FiniteGeneratingSections
import KltDP.Geometry.InvertibleSectionNonvanishingPowers

/-!
# Arbitrarily large globally generated actual powers of a semiample sheaf

Positive powers of the original generating sections retain their actual
nonvanishing opens. The existing nonvanishing-cover epimorphism criterion
therefore generates each positive power, without compactness. The original
Picard comparison then identifies an iterated power with its actual total
exponent. No base field or geometric finiteness hypothesis is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SemiampleActualPowers

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowers InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- Powers of the actual generators generate every positive actual tensor power. -/
theorem isGloballyGenerated_power (hL : Positivity.IsGloballyGenerated L.obj)
    {n : ℕ} (hn : 0 < n) : Positivity.IsGloballyGenerated (power L n).obj := by
  obtain ⟨I, φ, hφ⟩ := hL
  letI := hφ
  let G := (_root_.SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).ofEpi φ
  have hcover : (⨆ a : G.I,
      nonvanishingOpen X (power L n) (powerSection L (G.s a) n)) = ⊤ := by
    calc
      _ = ⨆ a : G.I, nonvanishingOpen X L (G.s a) :=
        iSup_congr (fun a =>
          InvertibleSectionNonvanishingPowers.nonvanishingOpen_power L (G.s a) hn)
      _ = ⊤ := FiniteNonvanishingGenerators.iSup_nonvanishing_eq_top L G
  exact ⟨G.I, (power L n).obj.freeHomEquiv.symm (fun a => powerSection L (G.s a) n),
    FiniteGeneratingSections.epi_of_nonvanishing_cover (power L n)
      (fun a => powerSection L (G.s a) n) hcover⟩

/-- The original semiample witness supplies globally generated actual powers
with positive exponent exceeding any prescribed bound. -/
theorem exists_globallyGenerated_power_ge (hL : Positivity.IsSemiample L) (N : ℕ) :
    ∃ m : ℕ, 0 < m ∧ N ≤ m ∧ Positivity.IsGloballyGenerated (power L m).obj := by
  obtain ⟨m, hm, hG⟩ := (isSemiample_iff_power_globallyGenerated L).mp hL
  letI := Scheme.Modules.monoidalCategory X
  have hclass : (power (power L m) (N + 1)).toPic = (power L (m * (N + 1))).toPic := by
    simp only [power_toPic, pow_mul]
  have hsk : toSkeleton (power (power L m) (N + 1)).obj =
      toSkeleton (power L (m * (N + 1))).obj := by
    have h := congrArg (fun p : X.Pic => (p : Skeleton X.Modules)) hclass
    simpa only [InvertibleSheaf.toPic_val] using h
  obtain ⟨e⟩ := (show Nonempty ((power (power L m) (N + 1)).obj ≅
      (power L (m * (N + 1))).obj) from Quotient.exact hsk)
  have hbound : N + 1 ≤ m * (N + 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (N + 1) (show 1 ≤ m from hm)
  exact ⟨m * (N + 1), Nat.mul_pos hm (Nat.succ_pos N),
    (Nat.le_succ N).trans hbound,
    AmpleSerre.isGloballyGenerated_of_iso e
      (isGloballyGenerated_power (power L m) hG (Nat.succ_pos N))⟩

end KltDP.Geometry.SemiampleActualPowers
