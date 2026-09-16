import KltDP.Literature.Definitions.J2

/-!
The Stacks Project Authors, tag 07PJ, item (1), at frozen commit
540451b3e79a131df8eca4c4187448e49dcb262d: every field is J-2.
The J-1/J-2 and regular-local definitions are recorded in tags 07P7 and 00KU.
-/

universe u v

namespace KltDP.Literature.Stacks

/-- The literal field case of Stacks 07PJ(1), with independent ring universes. -/
axiom field_isJ2 (k : Type u) [instField : Field k] :
    KltDP.Literature.J2Ring.{u, v} k

end KltDP.Literature.Stacks
