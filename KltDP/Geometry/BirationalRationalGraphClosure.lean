import KltDP.Geometry.BirationalRationalMapOverTarget
import KltDP.Geometry.RationalMapGraphClosure

/-!
# The proper graph modification of the original birational correspondence

The input morphisms determine the original partial map by their actual
function-field inverses. The proved graph construction then gives a proper
modification over the original source, an extension over the original target,
and equality with that specific partial map on its unchanged domain.
No comparison map or compatibility equation is an additional input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalRationalGraphClosure

variable {T V X : Scheme.{u}} [IsIntegral T] [IsIntegral V] [IsIntegral X]
  [IsNoetherian T] (t : T ⟶ X) (v : V ⟶ X) [IsProper v]
  (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)

/-- The original inverse-over-`K(X)` correspondence admits an actual proper
graph modification, isomorphic over its original domain, with the original
over-`X` equation and original partial-map agreement. -/
theorem exists_proper_graph_extension :
    ∃ (G : Scheme.{u}) (p : G ⟶ T) (q : G ⟶ V)
      (j : (BirationalRationalMapOverTarget.partialMap t v ht hv).domain.toScheme ⟶ G),
      IsIntegral G ∧ IsProper p ∧
      IsIso (p ∣_ (BirationalRationalMapOverTarget.partialMap t v ht hv).domain) ∧
      j ≫ p = (BirationalRationalMapOverTarget.partialMap t v ht hv).domain.ι ∧
      j ≫ q = (BirationalRationalMapOverTarget.partialMap t v ht hv).hom ∧
      q ≫ v = p ≫ t :=
  RationalMapGraphClosure.exists_proper_extension t v
    (BirationalRationalMapOverTarget.partialMap t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

end KltDP.Geometry.BirationalRationalGraphClosure
