import KltDP.Geometry.FrobeniusMultiCentreKeelSemiample
import KltDP.Geometry.FrobeniusMultiCentreCompleteBirational
import KltDP.Examples.FrobeniusProjectivityProved

/-!
# The semiample original contracting line with projectivity supplied

The proved projectivity of the original finite-centre surface discharges
the last projectivity input of the contracting-line construction. Its
semiampleness and eventual birational complete systems retain only the
original field, characteristic and distinct-centre conditions.
The individually reviewed projectivity, RR and Keel literals remain in
the isolated candidate dependency boundary.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreContractingNef FrobeniusProjectivityProved

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- The same original contracting line, with its projectivity witness derived. -/
def originalLine : InvertibleSheaf (multiSurface (q + 1) n a) :=
  contractingLine q n a ha (originalMultiStructureProjective k (q + 1) n a)

/-- No projectivity or semiampleness hypothesis remains. -/
theorem originalLine_isSemiample (hn : 2 < n) :
    Positivity.IsSemiample (originalLine q n a ha) :=
  FrobeniusMultiCentreKeelSemiample.contractingLine_isSemiample q n a ha
    (originalMultiStructureProjective k (q + 1) n a) hn

/-- The complete systems of this same original line are eventually birational. -/
theorem originalLine_eventuallyBirational (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsProper (multiStructure (q + 1) n a) :=
      (originalMultiStructureProjective k (q + 1) n a).isProper
    KeelCompleteSystem.EventuallyBirational (multiStructure (q + 1) n a)
      (originalLine q n a ha) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsProper (multiStructure (q + 1) n a) :=
    (originalMultiStructureProjective k (q + 1) n a).isProper
  exact FrobeniusMultiCentreCompleteBirational.contractingLine_eventually_toImage_isBirationalScheme
    q n a ha (originalMultiStructureProjective k (q + 1) n a) hn

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
