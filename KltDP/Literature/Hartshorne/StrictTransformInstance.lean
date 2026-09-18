import KltDP.Manuscript.S04.IsolatedNodeExchangeTerminal

/-!
# Strict transforms under the contraction of a `(-1)`-curve (Hartshorne V.3.6, II.7.15; instance)

**Sources.** R. Hartshorne, *Algebraic Geometry*, GTM 52:
* Proposition V.3.6. "Let `C` be an effective divisor on `X`, `P ∈ X` a point of multiplicity `r`
  on `C`, `π : X̃ → X` the monoidal transformation of `X` at `P`, `C̃` the strict transform. Then
  `π^*C = C̃ + rE`."
* Definition before V.3.6 / II.7.15 (strict transform): `C̃` is the closure of `π^{-1}(C − P)`;
  Corollary II.7.15 identifies `C̃` with the blowup of `C` at `P ∩ C`; every irreducible curve of
  `X̃` other than `E` is the strict transform of its image (its image is an irreducible curve, and
  the curve is the closure of the preimage of the image minus `P`).
* Multiplicity: `μ_P(C) = 0` iff `P ∉ C`, `μ_P(C) ≥ 1` iff `P ∈ C` (definition, V.3, p. 388).
* Proposition II.7.13(a)/II.7.14: the blowup of a scheme along an invertible ideal sheaf is an
  isomorphism; for a curve `C` regular at `P` (equivalently `μ_P(C) ≤ 1`), the ideal of `P` in
  `C` is invertible, so `C̃ ≅ C` over `k`.
* Proposition V.5.3 / Castelnuovo V.5.7: a contraction `b : S → T` of a `(-1)`-curve `E` between
  nonsingular projective surfaces is the monoidal transformation of `T` at the point `b(E)`.

**Instance admitted** (`hasContractionLifts_instance`): for every actual contraction
`b : S → T` (`IsContraction S T b E`) of a `(-1)`-curve `E` between actual regular projective
surfaces over an algebraically closed field, the strict transform data
`KltDP.Manuscript.S04.ContractionLifts hb hS` exists: `lift Q` (strict transform), `mult Q`
(multiplicity of `Q` at the centre), with `b(lift Q) = Q`, surjectivity onto curves `≠ E`,
`b^*Q = lift Q + (mult Q) E` (V.3.6 as Cartier divisors on `S`), `mult Q = 0` iff `Q` misses the
centre (with the `> 0` form when it meets it), and `lift Q ≅ Q` over `k` when `mult Q ≤ 1`.
Each field is one of the published statements above, applied to `b` viewed as the monoidal
transformation at `b(E)` (V.5.3); the specialisation of "point of multiplicity `r`" to the actual
intersection-number/disjointness vocabulary is documented on the fields of `ContractionLifts`.
This is the last literature admission of the formalization (with `Tanaka.contraction_44_instance`,
`Hartshorne.hurwitz_degreeTwo_projectiveLine_instance`, `Stacks.blowupRegularPoint_literal`).
-/

set_option autoImplicit false

universe u

namespace KltDP.Literature.Hartshorne

/-- **Hartshorne V.3.6 + II.7.15 + II.7.13 (strict transforms), instance** for contractions of
`(-1)`-curves between regular projective surfaces over an algebraically closed field. -/
axiom hasContractionLifts_instance (k : Type u) [Field k] [IsAlgClosed k] :
    KltDP.Manuscript.S04.HasContractionLifts k

end KltDP.Literature.Hartshorne

#print axioms KltDP.Literature.Hartshorne.hasContractionLifts_instance
