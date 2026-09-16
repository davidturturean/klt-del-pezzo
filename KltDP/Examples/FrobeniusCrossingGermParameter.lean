import KltDP.Examples.FrobeniusVerticalContactStalk
import KltDP.Geometry.GluedSubschemeStalkKernel
import KltDP.Geometry.RationalTreePicardRestrictStalk

/-!
# The crossing germ is the local parameter (BRIEF31)

`crossing_contact_length` and `crossing_contact_length_pow` both take the hypothesis
`crossingStalkEquiv n m c f = localParameter c`. Discharging it for a germ that comes from an actual
section — rather than for a germ *defined* through the stalk equivalence, which is circular — is the
step the three rows need.

The accepted `graphFiberGerm` shows both kinds. Its identification `graphStalkLocalEquiv_fiberGerm` is
`RingEquiv.apply_symm_apply`, because the germ is defined as the inverse image of the wanted element;
the honest version is earned separately in `graphFiberGerm_pullback`, through the actual chart ring
map. This module does the second kind on the `P¹` side, where the accepted
`openImmersionStalkLocalizationEquiv_germ` applies directly:

> the germ at `j.base p` of a section `s` of the chart open `j ''ᵁ ⊤` is
> `algebraMap R (Localization.AtPrime p.asIdeal) (chartSectionsEquiv j s)`.

At `j = polynomialLineChart` and `p = parameterSchemePoint c` the target is definitionally
`parameterLocalRing c` (an `abbrev` for `Localization.AtPrime (parameterPointIdeal c)`), and
`localParameter c` is by definition `algebraMap _ _ (X - C c)`. So the identification reduces to a
ring-level statement about `chartSectionsEquiv`, with no stalk transport at all.

* `lineParameterSection c` — the section `t - c` of the chart open of `P¹`, built as the
  `chartSectionsEquiv`-preimage of `X - C c`;
* **`lineStalkLocalEquiv_parameterGerm`** — its germ is `localParameter c`;
* **`crossingStalkEquiv_germ_lineParameterSection`** — the same germ, pulled back to `B_n` along the
  accepted isomorphism, is carried by `crossingStalkEquiv` to `localParameter c`. This is the
  hypothesis the contact-length lemmas ask for.
* `crossing_contact_length_lineParameter`, `crossing_contact_length_pow_lineParameter` — the lengths
  with the hypothesis discharged.

The `P¹` side is where the content is: the section is pulled back along an isomorphism, so the germ
transport is `Scheme.stalkMap_germ_apply` and nothing is lost.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusCrossingGermParameter

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusProjectivePoints FrobeniusGraphContact FrobeniusGraphStalkContact
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformIsoProjectiveLine
open FrobeniusVerticalContactLength FrobeniusVerticalContactStalk

variable {k : Type u} [Field k]

/-- The section `t - c` of the chart open of `P¹`, as the chart-ring preimage of `X - C c`. -/
def lineParameterSection (c : k) :
    Γ(projectiveSpace k 1, polynomialLineChart (k := k) ''ᵁ ⊤) :=
  (chartSectionsEquiv (polynomialLineChart (k := k))).symm (Polynomial.X - Polynomial.C c)

/-- The parameter point lies in the chart open. -/
theorem lineParamPoint_mem (c : k) :
    lineParamPoint c ∈ polynomialLineChart (k := k) ''ᵁ ⊤ :=
  mem_chart_image_top _ _

/-- **The germ of `t - c` at the parameter point is the accepted `localParameter c`.** This is the
honest identification: the section exists first, and its germ is computed. -/
theorem lineStalkLocalEquiv_parameterGerm (c : k) :
    lineStalkLocalEquiv c
        ((projectiveSpace k 1).presheaf.germ (polynomialLineChart (k := k) ''ᵁ ⊤)
          (lineParamPoint c) (lineParamPoint_mem c) (lineParameterSection c)) =
      localParameter c := by
  have h := openImmersionStalkLocalizationEquiv_germ (polynomialLineChart (k := k))
    (parameterSchemePoint c) (lineParameterSection c)
  rw [lineParameterSection, RingEquiv.apply_symm_apply] at h
  exact h

section Graph

variable (n m : ℕ)

/-- The stalk map of the accepted isomorphism at the parameter point, as a ring equivalence. -/
def crossingStalkMapEquiv (c : k) :
    (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) ≃+*
      (projectiveSpace k 1).presheaf.stalk (lineParamPoint c) :=
  haveI : IsIso ((graphStrictIsoProjectiveLine (k := k) n m).inv.stalkMap (lineParamPoint c)) :=
    isIso_stalkMap_of_isIso _ _
  (asIso ((graphStrictIsoProjectiveLine (k := k) n m).inv.stalkMap
    (lineParamPoint c))).commRingCatIsoToRingEquiv

/-- The germ on `B_n` at the crossing point corresponding to the parameter section `t - c`. The
section on `P¹` is a genuine one; only the transport across the isomorphism is inverted. -/
def crossingGerm (c : k) :
    (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) :=
  (crossingStalkMapEquiv n m c).symm
    ((projectiveSpace k 1).presheaf.germ (polynomialLineChart (k := k) ''ᵁ ⊤)
      (lineParamPoint c) (lineParamPoint_mem c) (lineParameterSection c))

/-- **The crossing germ is the local parameter.** The stalk map of the accepted isomorphism carries
the germ of the pulled-back section to the germ downstairs (`Scheme.stalkMap_germ_apply`), and that
germ is `localParameter c` by `lineStalkLocalEquiv_parameterGerm`. -/
theorem crossingStalkEquiv_germ_lineParameterSection (c : k) :
    crossingStalkEquiv n m c (crossingGerm n m c) = localParameter c := by
  rw [← lineStalkLocalEquiv_parameterGerm c]
  change lineStalkLocalEquiv c (crossingStalkMapEquiv n m c (crossingGerm n m c)) = _
  rw [crossingGerm, RingEquiv.apply_symm_apply]

/-- **Vertical contact length one along `B`, with no hypothesis left.** -/
theorem crossing_contact_length_lineParameter (c : k) :
    Module.length ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
      ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) ⧸
        Ideal.span {crossingGerm n m c}) = 1 :=
  crossing_contact_length n m c (crossingGerm n m c)
    (crossingStalkEquiv_germ_lineParameterSection n m c)

end Graph

end KltDP.Examples.FrobeniusCrossingGermParameter

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphContact
open FrobeniusGlobalStrictTransform FrobeniusVerticalContactStalk
open FrobeniusCrossingGermParameter

/-- **F29: the germ of the vertical parameter section at the crossing point of `B` is the local
parameter, and its contact length is one** — the hypothesis of the contact-length lemmas, discharged
for a germ that comes from an actual section. -/
theorem f29_crossing_germ_parameter (k : Type u) [Field k] (n m : ℕ) (c : k) :
    crossingStalkEquiv n m c (crossingGerm n m c) = localParameter c ∧
    Module.length ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
      ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) ⧸
        Ideal.span {crossingGerm n m c}) = 1 :=
  ⟨crossingStalkEquiv_germ_lineParameterSection n m c,
    crossing_contact_length_lineParameter n m c⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_crossing_germ_parameter_universe_check (k : Type u) [Field k] (n m : ℕ) (c : k) :
    True := by
  have _ := f29_crossing_germ_parameter.{u} k n m c
  trivial

end KltDP.Examples
