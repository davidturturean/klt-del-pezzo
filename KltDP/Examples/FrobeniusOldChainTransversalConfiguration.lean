import KltDP.Geometry.TransversalConfigurationComponentComplement
import KltDP.Examples.FrobeniusMultiCentreOldChainGeometry

/-!
# Actual ambient crossing equations for the old exceptional chain

Remove exactly the newest component from the already proved original
exceptional-chain configuration. The inherited equations remain in the
stalk of the original multicentre surface, with its actual old-chain map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreOldChain

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusMultiCentreSurface FrobeniusMultiCentreChainPicard
  FrobeniusMultiCentreChainTransversal

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- The original reduced old-only chain has no triple points, and at each
crossing its actual surface-stalk kernel is the product of two parameters
generating the ambient maximal ideal. No projectivity or characteristic
hypothesis is needed. -/
theorem oldChain_transversalConfiguration (i : Fin n) :
    TransversalConfiguration (oldChainInclusion q n a ha i) := by
  exact transversalConfiguration_componentComplement (towerChain q n a ha i)
    (towerComponents q n a ha i (Fin.last q)) (towerChainInclusion q n a ha i)
    (CurveChain.transversalConfiguration (multiSurface (q + 1) n a) q
      (FrobeniusMultiCentreChainPicard.chainCurve q n a ha i)
      (chainData q n a ha (singlePoints q n a ha) i) (towerTransversal q n a ha i))

end KltDP.Examples.FrobeniusMultiCentreOldChain
