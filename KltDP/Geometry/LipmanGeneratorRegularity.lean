import KltDP.Geometry.RegularLocalDimensionTwo
import KltDP.Geometry.DivisorOrder
import KltDP.Geometry.ProperBirationalDimension

/-!
# Generator regularity on an original proper birational source

The existing dimension theorem bounds the actual source stalks. The proved
local-domain equivalence then converts the published generator definition
of regularity to the project's cotangent definition on the same source.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.LipmanIdentityNormalization

/-- Convert the source's regularity predicate after deriving dimension
from the same original proper birational morphism. -/
theorem regularPoint_of_generatorRegular_proper_birational
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (S : Scheme.{u}) [IsIntegral S]
    (π : S ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (hreg : ∀ s : S, RegularLocalByGenerators (S.presheaf.stalk s)) :
    ∀ s : S, RegularPoint S s := by
  have hdim : topologicalKrullDim S = 2 :=
    (topologicalKrullDim_eq_of_proper_birational π X.structureMorphism hbir).trans
      X.dimension_two
  intro s
  letI : IsDomain (S.presheaf.stalk s) := integralSchemeStalk_isDomain S s
  exact regularLocal_of_generators_of_dimension_le_two
    ((ringKrullDim_stalk_le_topologicalKrullDim S s).trans_eq hdim) (hreg s)

end KltDP.Geometry.LipmanIdentityNormalization

#print axioms KltDP.Geometry.LipmanIdentityNormalization.regularPoint_of_generatorRegular_proper_birational
