import KltDP.Geometry.CanonicalWeilClassIndependent
import KltDP.Geometry.QAmpleWeilClassInvariant
import KltDP.Geometry.DelPezzoType

/-!
# Testing the intrinsic klt del Pezzo predicate at a genuine canonical divisor

Any canonical representative witnessing the intrinsic predicate has the
same actual Weil class as the specified canonical divisor. Its negative
ample Cartier numerator therefore transfers by a principal correction.
-/

noncomputable section

universe u

namespace KltDP.Geometry

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Once the actual all-normal-model KLT statement is proved for a
canonical divisor, intrinsic klt del Pezzo is exactly Q-ampleness of its
negative, independently of the existential canonical representative. -/
theorem isKltDelPezzo_iff_neg_qAmple_of_isKltWithCanonicalDivisor
    (X : NormalProjectiveSurface k) (KX : X.WeilDivisor)
    (hKX : IsKltWithCanonicalDivisor X KX) :
    IsKltDelPezzo X ↔ X.QAmple (-rationalizeWeilDivisor X KX) := by
  constructor
  · intro hX
    obtain ⟨K', hK', hample⟩ := (isLogDelPezzoPair_zero_iff X).mp hX
    exact (X.qAmple_neg_integral_iff_of_weilClass_eq K' KX
      (IsCanonicalWeilDivisor.weilClassMap_eq hK'.1 hKX.1)).mp hample
  · intro hample
    exact (isLogDelPezzoPair_zero_iff X).mpr ⟨KX, hKX, hample⟩

end KltDP.Geometry
