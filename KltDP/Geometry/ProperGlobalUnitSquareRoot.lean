import KltDP.Geometry.ProperGlobalSectionsConstants
import Mathlib.Algebra.Group.Commute.Units

/-!
# Actual unit roots of original global functions

The original proper structure map makes global functions constants over the
algebraically closed field. Its bijective scalar map and the field root
theorem produce roots in the original section ring, with no chosen field
structure on that ring and no supplied square-root section.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProperGlobalUnitSquareRoot

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
  [UniversallyClosed f] [LocallyOfFiniteType f]

include f in
/-- Every original global unit has an actual unit square root. -/
theorem exists_sq (a : Γ(X, ⊤)ˣ) : ∃ b : Γ(X, ⊤)ˣ, b ^ 2 = a := by
  obtain ⟨c, hc⟩ := (baseFieldToGlobalSections_bijective f).surjective (a : Γ(X, ⊤))
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by decide)
  have hsq : (baseFieldToGlobalSections f d) ^ 2 = (a : Γ(X, ⊤)) := by
    rw [← map_pow, hd, hc]
  have hunit : IsUnit (baseFieldToGlobalSections f d) :=
    (isUnit_pow_iff (show (2 : ℕ) ≠ 0 by decide)).mp (hsq.symm ▸ a.isUnit)
  obtain ⟨b, hb⟩ := hunit
  refine ⟨b, Units.ext ?_⟩
  change (b : Γ(X, ⊤)) ^ 2 = (a : Γ(X, ⊤))
  rw [hb]
  exact hsq

end KltDP.Geometry.ProperGlobalUnitSquareRoot
