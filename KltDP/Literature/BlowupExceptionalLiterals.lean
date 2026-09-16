import KltDP.Geometry.Resolution
import KltDP.Geometry.PointBlowupExceptionalIdeal
import KltDP.Geometry.PicardEulerValue

/-!
# Stacks literals for the blowup of a regular point of a surface (F10, E4)

`Prop`-valued structures used only as hypotheses; nothing is assumed here. The exact texts, tags and
fetch date (2026-09-11, `https://stacks.math.columbia.edu/tag/<tag>`) and every specialisation step
are recorded in `laneE/F10_LITERALS.md`.

* `BlowupChartRegularLiteral` — Stacks 0AGR (Lemma 54.3.2) for the accepted glued point blowup
  `KltDP.Geometry.PointBlowupGluing.scheme` of a regular surface at a closed point of an affine
  chart. This is the form of 0AGR that can be used *before* the blowup is packaged as a surface;
  the E2 literal `BlowupRegularLiteral` states the same lemma for a morphism already known to be
  an `IsPointBlowupAt` of two `NormalProjectiveSurface`s.
* `BlowupRegularPointLiteral` — Stacks 0AGQ (Lemma 54.3.1) for the same blowup: the centre fibre is
  `P¹` over the residue field, and the conormal sheaf of the exceptional divisor is
  `(r|_E)^* O_{P¹}(1)`, recorded in degree form (Euler difference `1` on `P¹`, the degree of
  `O_{P¹}(1)` in the accepted Stacks 0AYR convention `deg L = χ(L) − χ(O)`).

Neither literal mentions blowup charts of `PointBlowupChart` form: both quantify over the accepted
gluing data `(j, q, hclosed)` of `KltDP.Geometry.PointBlowupGluing`, which is what a chart carries.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Literature.Stacks

variable (k : Type u) [Field k]

/-- Stacks 0AGR, Lemma 54.3.2: "Let `(A, 𝔪, κ)` be a regular local ring of dimension `2`. Let
`f : X → S = Spec(A)` be the blowing up of `A` in `𝔪`. Then `X` is an irreducible regular scheme."
Encoded for the accepted glued point blowup of a regular `NormalProjectiveSurface k` at the closed
point `j.base q` of an affine chart: every point of `PointBlowupGluing.scheme j q hclosed` is
regular. Specialisation: irreducibility is the accepted `surface_scheme_isIntegral`; off the centre
the blowup is an isomorphism (accepted `projection_restrict_puncture_isIso`), and over the centre
blowing up commutes with the flat base change `Spec 𝒪_{S,x} → S` (Stacks 0805, Lemma 31.33.3), the
local ring `𝒪_{S,x}` at a closed point of a regular surface being regular of dimension two. -/
structure BlowupChartRegularLiteral : Prop where
  regular : ∀ (S : NormalProjectiveSurface k) (R : Type u) [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ S.toScheme) [IsOpenImmersion j] (q : PrimeSpectrum R)
    [q.asIdeal.IsMaximal] (hclosed : IsClosed ({j.base q} : Set S.toScheme)),
    (∀ x : S.Point, RegularPoint S.toScheme x) →
      ∀ y : PointBlowupGluing.scheme j q hclosed,
        RegularPoint (PointBlowupGluing.scheme j q hclosed) y

/-- Stacks 0AGQ, Lemma 54.3.1: "Let `(A, 𝔪, κ)` be a regular local ring of dimension `2`. Let
`f : X → S = Spec(A)` be the blowing up of `A` in `𝔪` wotj [sic, as served] exceptional divisor
`E`. There is a closed immersion `r : X → P¹_S` over `S` such that `r|_E : E → P¹_κ` is an
isomorphism, `O_X(E) = O_X(−1) = r^*O_{P¹}(−1)`, and `C_{E/X} = (r|_E)^*O_{P¹}(1)` and
`N_{E/X} = (r|_E)^*O_{P¹}(−1)`."

Encoded for the accepted glued point blowup of a regular `NormalProjectiveSurface k` at the closed
point `j.base q`, in the two clauses that the consumers use:

* `r|_E : E ≅ P¹_κ` with `κ = k`: an isomorphism `e` of the accepted centre fibre
  `PointBlowupGluing.globalCenterFiber j q hclosed` with `projectiveSpace k 1` *over `k`*, the
  `k`-structure of the fibre being its inclusion into the blowup followed by the blowdown and the
  structure morphism of `S`. Specialisation: `κ(j.base q) = k` because `k` is algebraically closed
  and the point is closed on a finite-type `k`-scheme (accepted
  `KltDP.Geometry.closedPointResidueFieldIso`), so `P¹_κ` is `P¹_k` over `k`.
* `C_{E/X} = (r|_E)^*O_{P¹}(1)`: the accepted conormal sheaf `schemeConormalSheaf` of the centre
  fibre, transported to `P¹` along `e`, has degree one — recorded as the Euler difference
  `χ(C_{E/X}) − χ(O_{P¹}) = 1` of Stacks 0AYR, which is the degree of `O_{P¹}(1)`. The normal-sheaf
  clause is the dual statement and is not encoded separately; the accepted `O_X(E)` clause is not
  used. Specialisation debt: the identification of the conormal sheaf `I/I²` of `E` with
  `(r|_E)^*O_{P¹}(1)` is used only through its degree, and the degree of `O_{P¹}(1)` on `P¹` is `1`
  (accepted `KltDP.Geometry.ProjectiveLineDegree.degree` of `ProjectiveLineDegreeExponent.lean`).
-/
structure BlowupRegularPointLiteral : Prop where
  exceptional_projectiveLine : ∀ (S : NormalProjectiveSurface k) (R : Type u) [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ S.toScheme) [IsOpenImmersion j] (q : PrimeSpectrum R)
    [q.asIdeal.IsMaximal] (hclosed : IsClosed ({j.base q} : Set S.toScheme)),
    (∀ x : S.Point, RegularPoint S.toScheme x) →
      ∃ e : PointBlowupGluing.globalCenterFiber j q hclosed ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 =
            PointBlowupGluing.globalCenterFiberι j q hclosed ≫
              PointBlowupGluing.projection j q hclosed ≫ S.structureMorphism ∧
          eulerCharacteristic (projectiveSpaceToSpec k 1)
              ((schemeModulePullback e.inv).obj
                (schemeConormalSheaf (PointBlowupGluing.globalCenterFiberι j q hclosed))) -
            eulerCharacteristic (projectiveSpaceToSpec k 1)
              (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = 1

end KltDP.Literature.Stacks
