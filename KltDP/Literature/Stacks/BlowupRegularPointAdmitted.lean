import KltDP.Literature.BlowupExceptionalLiterals

/-!
# Admission of the queued point-blowup literal (Stacks 0AGQ / 0AGR / 0C5P; Hartshorne V.3.1)

`KltDP.Literature.Stacks.BlowupRegularPointLiteral k` is the union's own queued literature literal
(a `Prop` structure whose docstring, in `Literature/BlowupExceptionalLiterals.lean`, records the
published statements and every specialisation): the exceptional fibre of the blowup of a regular
projective surface at a closed point is `P¹_k` over `k` and its conormal sheaf has degree one,
i.e. `E ≅ P¹` and `E² = −1`.

**Sources.** Stacks Project Tag 0AGQ (blowing up a regular closed point of a regular surface: the
exceptional fibre is a projective line over the residue field), Tag 0AGR / 0C5P (its conormal sheaf
is `O(1)`); Hartshorne, *Algebraic Geometry*, Proposition V.3.1 (the blowup of a point on a
nonsingular surface is a nonsingular surface with exceptional curve `E ≅ P¹`, `E² = −1`).

Admitted here as an `axiom` exactly in the union's queued form. It is consumed only through
`KltDP.Manuscript.S04.hasPointBlowups_of_literal` (existence of the point blowup as a contraction
with a `(-1)`-curve centre fibre), for the terminal case of Theorem 4.6.
-/

set_option autoImplicit false

universe u

namespace KltDP.Literature.Stacks

/-- **Stacks 0AGQ/0AGR/0C5P, Hartshorne V.3.1** (the union's queued literal, admitted). -/
axiom blowupRegularPoint_literal (k : Type u) [Field k] [IsAlgClosed k] : BlowupRegularPointLiteral k

end KltDP.Literature.Stacks

#print axioms KltDP.Literature.Stacks.blowupRegularPoint_literal
