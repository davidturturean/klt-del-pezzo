import KltDP.Geometry.RegularLocalUFD

/-!
# Factoriality of the original stalk at a regular point

The canonical regular-local adapter applies to the original structure-sheaf
stalk. Its existing domain instance is retained. These are explicit theorem
applications, not global typeclass instances; normality alone does not supply
the regularity premise.
-/

universe u

namespace KltDP.Geometry

/-- An actual regular-point stalk with its existing domain structure is a UFD. -/
theorem regularPoint_stalk_uniqueFactorizationMonoid
    (X : AlgebraicGeometry.Scheme.{u}) (x : X)
    [IsDomain (X.presheaf.stalk x)] (hx : RegularPoint X x) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  regularLocal_uniqueFactorizationMonoid (X.presheaf.stalk x) hx

namespace NormalProjectiveSurface

/-- The original normal-surface stalk is factorial at an actual regular point. -/
theorem stalk_uniqueFactorizationMonoid_of_regularPoint
    {k : Type u} [Field k] (X : NormalProjectiveSurface k) (x : X.Point)
    (hx : RegularPoint X.toScheme x) :
    UniqueFactorizationMonoid (X.stalk x) :=
  regularPoint_stalk_uniqueFactorizationMonoid X.toScheme x hx

/-- Regularity at every actual point supplies exactly the factorial-stalk
family required by the constructed divisor comparisons. -/
theorem stalks_uniqueFactorizationMonoid_of_regular
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x) :
    ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) :=
  fun x => X.stalk_uniqueFactorizationMonoid_of_regularPoint x (hregular x)

/-- On the existing normal surface, regularity of all actual closed points
implies regularity at every point: a nonregular point would be closed by
the previously proved normal-surface codimension argument. -/
theorem regularPoints_of_closedPoints_regular
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (hclosed : ∀ x : X.Point, IsClosed ({x} : Set X.Point) →
      RegularPoint X.toScheme x) :
    ∀ x : X.Point, RegularPoint X.toScheme x := by
  intro x
  by_contra hx
  exact hx (hclosed x (singularPoint_isClosed X x hx))

end NormalProjectiveSurface
end KltDP.Geometry
