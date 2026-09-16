import KltDP.Geometry.RegularLocalDimensionTwo
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
Literal statement of Stacks Project, Tag 0AG0, at revision
540451b3e79a131df8eca4c4187448e49dcb262d.
The UFD conclusion includes the domain property (Tag 034S).
The generator definition of regular local ring is Tag 00KU.
-/

universe u

namespace KltDP.Literature.Stacks

axiom regularLocal_isUFD
    (R : Type u) [instCommRing : CommRing R] [instLocalRing : IsLocalRing R]
    (hregular : KltDP.Geometry.RegularLocalByGenerators R) :
    ∃ hDomain : IsDomain R,
      letI : IsDomain R := hDomain
      UniqueFactorizationMonoid R

end KltDP.Literature.Stacks
