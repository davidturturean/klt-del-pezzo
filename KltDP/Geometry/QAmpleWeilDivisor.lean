import KltDP.Geometry.CartierPicardEndpointRational
import KltDP.Geometry.CartierDivisorTrivialization
import KltDP.Geometry.AmpleSerre

/-!
# Q-ampleness of an original rational Weil divisor

A positive integral multiple must equal the Weil divisor of an actual
Cartier divisor whose associated invertible sheaf is ample. The positive
index, original Cartier-to-Weil map and actual sheaf are retained. This
implies the existing Q-Cartier predicate by its proved denominator criterion.
No regularity or algebraically closed field hypothesis is needed here.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- A rational Weil divisor is ample when one positive integral multiple
is represented by an actual ample Cartier divisor. -/
def QAmple (D : X.RationalWeilDivisor) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ A : CartierDivisor X.toScheme,
    rationalizeWeilDivisor X (X.cartierToWeilHom A) = n • D ∧
      AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A)

/-- Q-ampleness supplies the original Q-Cartier membership proof. -/
theorem QAmple.qCartier {D : X.RationalWeilDivisor} (h : X.QAmple D) : X.QCartier D := by
  obtain ⟨n, hn, A, hA, _⟩ := h
  exact (X.qCartier_iff_exists_positive_multiple D).mpr ⟨n, hn, A, hA⟩

/-- The original Weil divisor of an ample Cartier divisor is Q-ample. -/
theorem qAmple_cartierToWeil (A : CartierDivisor X.toScheme)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A)) :
    X.QAmple (rationalizeWeilDivisor X (X.cartierToWeilHom A)) := by
  exact ⟨1, Nat.zero_lt_one, A, (one_smul ℕ _).symm, hA⟩

end KltDP.Geometry.NormalProjectiveSurface
