import KltDP.Literature.KeelCompleteSystem
import KltDP.Geometry.FrobeniusMultiCentreKeelExceptional

/-!
# Semiampleness of the original Frobenius contracting line

The proved whole exceptional-scheme restriction is supplied to the exact
published Keel theorem. The original surface, field, line, and nefness
are retained. No semiampleness or contraction witness is assumed.
This consumer belongs to the isolated, individually reviewed literature branch.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.FrobeniusMultiCentreKeelSemiample

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreContractingNef

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The actual nef positive-square contracting line M is semiample on the original surface. -/
theorem contractingLine_isSemiample (hn : 2 < n) :
    Positivity.IsSemiample (contractingLine q n a ha hproj) := by
  letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
  exact (KltDP.Literature.Keel.semiampleness_completeSystem_literal
    (q + 1) (Nat.succ_pos q) _ (multiStructure (q + 1) n a) hproj
    (contractingLine q n a ha hproj) (contractingLine_isNef q n a ha hproj hn.le)).mpr
      (FrobeniusMultiCentreKeelExceptional.contractingLine_exceptionalRestriction_semiample
        q n a ha hproj hn)

end KltDP.Geometry.FrobeniusMultiCentreKeelSemiample
