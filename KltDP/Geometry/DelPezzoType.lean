import KltDP.Geometry.NormalModelKltPair
import KltDP.Geometry.QAmpleWeilDivisor

/-!
# Del Pezzo type and the original zero-boundary specialization

This implements Bernasconi, arXiv:1709.09238v3, Definition 2.1(5), using
the actual effective rational pair and a positive ample Cartier multiple
of the negative log-canonical divisor. The same canonical representative
is used in the all-normal-model discrepancy test and in ampleness.

The pair predicate currently has an algebraically closed base, which is
also the base scope of Lemma 5.1. These definitions assert no rationality,
cohomology vanishing, exceptional forest or Picard-number result.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A log del Pezzo pair, using the same actual canonical divisor in its
KLT test and its ample negative log-canonical divisor. -/
def IsLogDelPezzoPair (X : NormalProjectiveSurface k)
    (boundary : X.RationalWeilDivisor) : Prop :=
  ∃ KX : X.WeilDivisor,
    IsKltPairWithCanonicalDivisor X KX boundary ∧
      X.QAmple (-(rationalizeWeilDivisor X KX + boundary))

/-- A surface of del Pezzo type admits an actual effective rational
boundary making it a log del Pezzo pair. Effectivity is in the pair test. -/
def IsDelPezzoType (X : NormalProjectiveSurface k) : Prop :=
  ∃ boundary : X.RationalWeilDivisor, IsLogDelPezzoPair X boundary

/-- The source definition of a klt del Pezzo surface takes boundary zero. -/
def IsKltDelPezzo (X : NormalProjectiveSurface k) : Prop :=
  IsLogDelPezzoPair X 0

/-- At boundary zero the log-pair input is exactly the original KLT test
and Q-ampleness of the negative of that same canonical divisor. -/
theorem isLogDelPezzoPair_zero_iff (X : NormalProjectiveSurface k) :
    IsLogDelPezzoPair X 0 ↔
      ∃ KX : X.WeilDivisor, IsKltWithCanonicalDivisor X KX ∧
        X.QAmple (-rationalizeWeilDivisor X KX) := by
  simp only [IsLogDelPezzoPair, isKltPairWithCanonicalDivisor_zero_iff, add_zero]

/-- The original zero-boundary surface is a surface of del Pezzo type. -/
theorem isDelPezzoType_of_isKltDelPezzo (X : NormalProjectiveSurface k)
    (hX : IsKltDelPezzo X) : IsDelPezzoType X :=
  ⟨0, hX⟩

/-- An actual ample Cartier numerator of the original negative canonical
divisor supplies the zero-boundary del Pezzo-type input. -/
theorem isDelPezzoType_of_klt_ample_multiple (X : NormalProjectiveSurface k)
    (KX : X.WeilDivisor) (hklt : IsKltWithCanonicalDivisor X KX)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : rationalizeWeilDivisor X (X.cartierToWeilHom A) =
      n • (-rationalizeWeilDivisor X KX))
    (hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A)) :
    IsDelPezzoType X := by
  apply isDelPezzoType_of_isKltDelPezzo X
  apply (isLogDelPezzoPair_zero_iff X).mpr
  exact ⟨KX, hklt, n, hn, A, hA, hample⟩

end KltDP.Geometry
