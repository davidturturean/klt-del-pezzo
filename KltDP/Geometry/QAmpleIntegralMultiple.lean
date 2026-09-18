import KltDP.Geometry.QAmpleWeilDivisor

/-!
# Exact ample integral multiples imply Q-ampleness

Rationalize the actual Cartier-to-Weil equality. The Cartier divisor, its
ample associated line and the original positive index are all retained.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- An exact ample Cartier multiple in the original integral Weil group
is an ample numerator for the corresponding rational divisor. -/
theorem qAmple_of_ample_integral_multiple (D : X.WeilDivisor)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.cartierToWeilHom A = n • D)
    (hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A)) :
    X.QAmple (rationalizeWeilDivisor X D) := by
  refine ⟨n, hn, A, ?_, hample⟩
  exact (congrArg (rationalizeWeilDivisor X) hA).trans
    ((rationalizeWeilDivisor X).map_nsmul D n)

end KltDP.Geometry.NormalProjectiveSurface
