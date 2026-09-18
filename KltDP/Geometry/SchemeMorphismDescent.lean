import KltDP.Geometry.LocallyRingedSpaceMorphismDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Actual scheme morphism descent through a proper surjection

This specializes ordinary locally ringed-space descent. The actual point map
is a quotient map because a proper surjection is closed and continuous.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Topology

universe u

namespace KltDP.Geometry.SchemeMorphismDescent

variable {X Y Z : Scheme.{u}}

/-- An actual scheme morphism descends uniquely through a quotient map
whose original direct-image structure-sheaf map is an isomorphism. -/
theorem existsUnique_lift_of_quotient (b : X ⟶ Y) [IsIso b.c]
    (hb : IsQuotientMap b.base) (f : X ⟶ Z)
    (hconst : Function.FactorsThrough f.base b.base) :
    ∃! q : Y ⟶ Z, b ≫ q = f := by
  obtain ⟨q, hq, hu⟩ := LocallyRingedSpaceMorphismDescent.existsUnique_lift
    b.toLRSHom hb f.toLRSHom hconst
  refine ⟨Scheme.Hom.mk q, Scheme.Hom.ext' hq, ?_⟩
  intro m hm
  apply Scheme.Hom.ext'
  exact hu m.toLRSHom (congrArg Scheme.Hom.toLRSHom hm)

/-- A proper, surjective original morphism with its original pushforward-O
isomorphism has the required factorization property for every original
morphism constant on its point fibers. -/
theorem existsUnique_lift_of_proper (b : X ⟶ Y)
    [IsProper b] [Surjective b] [IsIso b.c] (f : X ⟶ Z)
    (hconst : Function.FactorsThrough f.base b.base) :
    ∃! q : Y ⟶ Z, b ≫ q = f :=
  existsUnique_lift_of_quotient b
    (b.isClosedMap.isQuotientMap b.continuous b.surjective) f hconst

end KltDP.Geometry.SchemeMorphismDescent

#print axioms KltDP.Geometry.SchemeMorphismDescent.existsUnique_lift_of_proper
