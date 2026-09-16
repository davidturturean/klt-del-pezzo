import KltDP.Literature.Stacks.RegularLocalUFD

/-!
# Factoriality of actual regular local rings and regular-point stalks

The published input uses the maximal-ideal generator definition. The generic
adapter first applies the proved forward bridge from the project's actual
cotangent-space definition. The domain and factoriality refer to the original
ring operations throughout. No regularity of a scheme point is inferred from
normality or smoothness in this module.
-/

universe u

namespace KltDP.Geometry

/-- The published conclusion for the project's actual regular-local predicate.
No domain or bound on dimension is assumed. -/
theorem regularLocal_isDomain_and_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsLocalRing R] (hregular : RegularLocal R) :
    ∃ hDomain : IsDomain R,
      letI : IsDomain R := hDomain
      UniqueFactorizationMonoid R := by
  exact KltDP.Literature.Stacks.regularLocal_isUFD R
    (regularLocalByGenerators_of_regularLocal hregular)

/-- When the actual domain instance is already available, proof irrelevance
identifies it with the returned domain proof; the ring operations are unchanged. -/
theorem regularLocal_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R]
    (hregular : RegularLocal R) : UniqueFactorizationMonoid R := by
  obtain ⟨hDomain, hUFM⟩ := regularLocal_isDomain_and_uniqueFactorizationMonoid R hregular
  exact hUFM

/-- The actual structure-sheaf stalk at a regular point is an integral domain
with unique factorization. Regularity at that point remains an explicit input. -/
theorem regularPoint_stalk_isDomain_and_uniqueFactorizationMonoid
    (X : AlgebraicGeometry.Scheme.{u}) (x : X) (hx : RegularPoint X x) :
    ∃ hDomain : IsDomain (X.presheaf.stalk x),
      letI : IsDomain (X.presheaf.stalk x) := hDomain
      UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  exact regularLocal_isDomain_and_uniqueFactorizationMonoid (X.presheaf.stalk x) hx

end KltDP.Geometry
