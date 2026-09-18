import KltDP.Geometry.CompleteLinearSystemImage
import KltDP.Geometry.BirationalAdapters
import KltDP.Geometry.InvertibleSheafSectionPowers

/-!
The complete-system meaning of bigness used in Keel's Definition-Lemma 0.0,
on original integral proper schemes. Every map is the original complete H0
basis map, on its actual non-base open, with its actual schematic image.
The eventual quantifier ranges over all sufficiently large powers.

These definitions do not alter Positivity.IsBig and assert no comparison
with growth bigness. No source theorem or literal is declared here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.KeelCompleteSystem

open CompleteLinearSystemSections InvertibleSheafSectionPowers

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]

local instance completeSystemDomain_isIntegral (L : InvertibleSheaf X)
    (hpos : 0 < dimension f L) :
    IsIntegral (CompleteLinearSystemMap.nonBaseOpen f L hpos).toScheme := by
  letI : Nonempty (CompleteLinearSystemMap.nonBaseOpen f L hpos) :=
    (CompleteLinearSystemMap.nonBaseOpen_nonempty f L hpos).to_subtype
  infer_instance

local instance completeSystemImage_isIntegral (L : InvertibleSheaf X)
    (hpos : 0 < dimension f L) :
    IsIntegral (SchematicImageGlued.image (CompleteLinearSystemMap.morphism f L hpos)) :=
  CompleteLinearSystemMap.image_isIntegral f L hpos

/-- The entire original complete system gives a birational map onto its actual image. -/
def Birational (L : InvertibleSheaf X) : Prop :=
  ∃ hpos : 0 < dimension f L,
    IsBirationalScheme (SchematicImageGlued.toImage (CompleteLinearSystemMap.morphism f L hpos))

/-- Every sufficiently large original tensor power has birational complete system. -/
def EventuallyBirational (L : InvertibleSheaf X) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → Birational f (power L n)

theorem birational_iff (L : InvertibleSheaf X) :
    Birational f L ↔ ∃ hpos : 0 < dimension f L,
      IsBirationalScheme (SchematicImageGlued.toImage (CompleteLinearSystemMap.morphism f L hpos)) :=
  Iff.rfl

theorem eventuallyBirational_iff (L : InvertibleSheaf X) :
    EventuallyBirational f L ↔ ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ hpos : 0 < dimension f (power L n),
        IsBirationalScheme (SchematicImageGlued.toImage
          (CompleteLinearSystemMap.morphism f (power L n) hpos)) := Iff.rfl

/-- The eventual condition supplies a positive power with its actual complete-system map. -/
theorem exists_positive_birational_power (L : InvertibleSheaf X)
    (h : EventuallyBirational f L) :
    ∃ n : ℕ, 0 < n ∧ Birational f (power L n) := by
  obtain ⟨N, hN, h⟩ := h
  exact ⟨N, hN, h N le_rfl⟩

/-- Package the existing eventual actual-map producers, deriving a positive threshold. -/
theorem eventuallyBirational_of_eventually_toImage (L : InvertibleSheaf X)
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (0 < dimension f (power L n)) ∧
        ∀ hpos : 0 < dimension f (power L n),
          IsBirationalScheme (SchematicImageGlued.toImage
            (CompleteLinearSystemMap.morphism f (power L n) hpos))) :
    EventuallyBirational f L := by
  obtain ⟨N, hN⟩ := h
  refine ⟨max N 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1), ?_⟩
  intro n hn
  obtain ⟨hpos, hbirational⟩ := hN n ((le_max_left N 1).trans hn)
  exact ⟨hpos, hbirational hpos⟩

end KltDP.Geometry.KeelCompleteSystem
