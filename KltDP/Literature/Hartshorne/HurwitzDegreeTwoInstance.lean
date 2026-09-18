import KltDP.Geometry.Surface
import KltDP.Geometry.PrimeCurveLineDegree
import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf

/-!
# Hurwitz's theorem for a degree-two map `P¹ → P¹` in characteristic `p > 2` (instance)

**Source.** R. Hartshorne, *Algebraic Geometry*, GTM 52, Chapter IV:
* Corollary 2.4 (Hurwitz). "Let `f : X → Y` be a finite separable morphism of curves. Let
  `n = deg f`. Then `2g(X) − 2 = n · (2g(Y) − 2) + deg R`", where `R = Σ_P length(Ω_{X/Y})_P · P`
  is the ramification divisor (Definition before 2.2).
* Proposition 2.2(b). "If `f` is tamely ramified at `P`, then `length(Ω_{X/Y})_P = e_P − 1`."
  (Here `X, Y` are nonsingular projective curves over an algebraically closed field `k`,
  Hartshorne's convention IV.1.)
(Also Stacks Project, Tag 0C1B, Riemann–Hurwitz in the different form, as cited by the manuscript,
`source/manuscript.tex` lines 2066–2099.)

**Instance admitted** (`hurwitz_degreeTwo_projectiveLine_instance`). `X = B`, an actual prime curve
of an actual normal projective surface `S` over an algebraically closed field `k` of
characteristic `p > 2`, with a given isomorphism `B ≅ P¹_k` over `k`; `Y = P¹_k`;
`f = g|_B = B.inclusion ≫ g` for a `k`-morphism `g : S → P¹`, of degree two (`hdeg`: the degree of
the pullback of `O(1)` to `B` is `2`; a nonconstant morphism of curves is finite, of this degree).
Specializations used to pass from the published statement to the admitted conclusion, recorded
here because the intermediate notions (separable degree, tameness, ramification index) are not
formalized in this library:
* `f` is separable: its inseparable degree is a power of `p` dividing `deg f = 2`, and `p > 2`.
* `f` is tamely ramified everywhere: every `e_P ≤ deg f = 2 < p`.
* `g(X) = g(Y) = 0`, so Hurwitz gives `Σ_P (e_P − 1) = 2`.
* A closed point `t ∈ Y` whose fibre `f^{-1}(t)` is a single point `x` has `e_x = deg f = 2`
  (`Σ_{x ↦ t} e_x = deg f`, II.6.9), contributing `1` to the sum.
Hence there are at most two closed points `t` with a singleton fibre — the admitted conclusion,
which is exactly the count Lemma 7.2 of the manuscript supplies to Theorem 7.5.
This is the second and last literature admission of the manuscript formalization; every other
input is the union's accepted literature literal set or `Tanaka.contraction_44_instance`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Literature.Hartshorne

/-- **Hartshorne IV.2.4 + IV.2.2(b), instance**: for a degree-two `k`-morphism `g|_B : B → P¹`
from a prime curve `B ≅ P¹` of a normal projective surface over an algebraically closed field of
characteristic `p > 2`, at most two closed points of `P¹` have a singleton fibre in `B`. -/
axiom hurwitz_degreeTwo_projectiveLine_instance {k : Type u} [Field k] [IsAlgClosed k]
    (p : ℕ) [CharP k p] (hp : 2 < p)
    (S : NormalProjectiveSurface k) (B : S.PrimeCurve)
    (e : B.toScheme ≅ projectiveSpace k 1) (he : e.hom ≫ projectiveSpaceToSpec k 1 = B.toSpec)
    (g : S.toScheme ⟶ projectiveSpace k 1) (hg : g ≫ projectiveSpaceToSpec k 1 = S.structureMorphism)
    (hdeg : B.lineDegree (pullbackInvertibleSheaf (B.inclusion ≫ g)
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)) = 2)
    (T : Finset (projectiveSpace k 1))
    (hT : ∀ t ∈ T, IsClosed ({t} : Set (projectiveSpace k 1)) ∧
      ∃ x : S.toScheme, (B : Set S.toScheme) ∩ g.base ⁻¹' {t} = {x}) :
    T.card ≤ 2

end KltDP.Literature.Hartshorne

#print axioms KltDP.Literature.Hartshorne.hurwitz_degreeTwo_projectiveLine_instance
