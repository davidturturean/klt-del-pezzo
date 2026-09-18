import KltDP.Geometry.KeelCompleteSystemBirational
import KltDP.Geometry.CompleteLinearSystemBignessReverse
import KltDP.Geometry.BignessPositivePowerReflection

/-!
# The actual eventual-birationality predicate implies original bigness

The shared predicate supplies the original complete-system map and its
actual birational image factor. The existing comparison gives original
section-growth bigness. For the eventual predicate, choose its positive
power and use the original positive-power reflection theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.KeelCompleteSystem

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]

/-- Birationality of the original complete system implies unchanged growth bigness
on the original positive-dimensional proper integral scheme. -/
theorem isBig_of_birational (L : InvertibleSheaf X)
    (hdim : 0 < Positivity.natDim X) (h : Birational f L) : Positivity.IsBig f L := by
  obtain ⟨hpos, hbir⟩ := h
  exact CompleteLinearSystemMap.isBig_of_toImage_isBirationalScheme f L hpos hbir hdim

/-- The shared eventual predicate implies unchanged bigness of the original line bundle. -/
theorem isBig_of_eventuallyBirational (L : InvertibleSheaf X)
    (hdim : 0 < Positivity.natDim X) (h : EventuallyBirational f L) :
    Positivity.IsBig f L := by
  obtain ⟨n, hn, hbir⟩ := exists_positive_birational_power f L h
  exact BirationalSectionGrowth.isBig_of_positive_power f L n hn
    (isBig_of_birational f (InvertibleSheafSectionPowers.power L n) hdim hbir)

end KltDP.Geometry.KeelCompleteSystem
