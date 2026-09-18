import KltDP.Geometry.KltResolutionPicardCohomologyInvariants

/-! The original klt del Pezzo minimal resolution satisfies K²+rho=10.
The actual irregularity is proved zero by the rational-or-ruled geometry;
the already proved original Noether formula then specializes. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsMinimalResolution

open ModuleCohomology SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- The original Noether relation needs no supplied rationality witness. -/
theorem noetherRelation_of_kltDelPezzo
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
    (hrank : X.picardRank = 1) (p : ℕ) [CharP k p] (hp : 0 < p)
    (K : CartierDivisor S.toScheme)
    (eK : cartierDivisorModule S.toScheme K ≅
      relativeDifferentialExterior S.structureMorphism 2) :
    S.NoetherRelationFor hmin.regular K := by
  have h1 := (hmin.picard_and_structure_invariants_of_kltDelPezzo hDP hrank p hp).2.2.2
  have hrel := (hmin.toIsResolution.noether_euler_relations_of_kltDelPezzo hDP K eK).1
  change S.intersectionPairing hmin.regular K K + (S.picardRank : ℤ) = 10
  simpa only [h1, Nat.cast_zero, mul_zero, sub_zero] using hrel

end KltDP.Geometry.IsMinimalResolution

#print axioms KltDP.Geometry.IsMinimalResolution.noetherRelation_of_kltDelPezzo
