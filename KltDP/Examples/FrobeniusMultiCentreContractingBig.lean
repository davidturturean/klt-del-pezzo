import KltDP.Examples.FrobeniusMultiCentreContractingNef
import KltDP.Geometry.NefPositiveSelfIntersectionBig

/-!
# Bigness of the original Frobenius class M

The independently proved actual nefness and positive square of M enter the
existing surface Riemann--Roch bigness theorem. Its conclusion uses the original
section-growth definition. This private consumer retains the existing RR
literature dependency of NefPositiveSelfIntersectionBig; it does not change
the accepted production literature boundary or assert a contraction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusMultiCentreContractingBig

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreContractingNef

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The actual M sheaf is big whenever there are more than two centres. -/
theorem contractingLine_isBig (hn : 2 < n) :
    Positivity.IsBig (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) := by
  letI : IsSmoothOfRelativeDimension 2
      (multiSurfaceSurface (q + 1) n a ha hproj).structureMorphism :=
    multiStructure_smoothTwo (q + 1) n a ha
  letI : IsSmooth (multiSurfaceSurface (q + 1) n a ha hproj).structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 _
  apply NefPositiveSelfIntersectionBig.isBig
    (multiSurfaceSurface (q + 1) n a ha hproj) (contractingLine q n a ha hproj)
    (contractingLine_isNef q n a ha hproj hn.le)
  change 0 < (multiSurfaceSurface (q + 1) n a ha hproj).picardPairing
    (multiSurfaceSurface (q + 1) n a ha hproj).regularPoints_of_isSmooth
    (cartierPicardClass (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
      (contractingDivisor q n a ha hproj))
    (cartierPicardClass (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
      (contractingDivisor q n a ha hproj))
  rw [(multiSurfaceSurface (q + 1) n a ha hproj).picardPairing_class,
    contractingDivisor_square]
  have hn' : (2 : ℤ) < n := by exact_mod_cast hn
  exact mul_pos (by positivity) (sub_pos.mpr hn')

end KltDP.Examples.FrobeniusMultiCentreContractingBig
