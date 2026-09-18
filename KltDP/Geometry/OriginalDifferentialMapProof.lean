import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport

/-!
# The original differential is independent of its triangle proof

Proof irrelevance is checked with abstract original schemes and morphisms,
before any concrete canonical isomorphism or LocalFrame is substituted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.OriginalDifferentialMapProof

/-- The same original differential with either proof of its actual
ground-field triangle. -/
theorem map_eq
    {k : Type u} [CommRing k] {A B : Scheme.{u}}
    (sA : A ⟶ Spec (CommRingCat.of k)) (sB : B ⟶ Spec (CommRingCat.of k))
    (q : B ⟶ A) (h h' : q ≫ sA = sB) (n : ℕ) :
    SchemeKaehlerExteriorPullbackTransport.map sA q sB h n =
      SchemeKaehlerExteriorPullbackTransport.map sA q sB h' n := rfl

end KltDP.Geometry.OriginalDifferentialMapProof

#check @KltDP.Geometry.OriginalDifferentialMapProof.map_eq
#print axioms KltDP.Geometry.OriginalDifferentialMapProof.map_eq
