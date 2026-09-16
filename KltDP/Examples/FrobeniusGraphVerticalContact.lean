import KltDP.Examples.FrobeniusGraphStalkContact
import KltDP.Geometry.DivisorOrderLength

/-!
# The vertical contact development on the graph, characteristic-free (BRIEF46)

The accepted contact development is entirely **second**-coordinate: `affineGraph_secondProjection`,
`fiberEquation`, `pulledFiberEquation`, `secondChartRingMap`, `polynomialGraphChart_secondProjection`,
`graphFiberGerm`, `graphFiberGerm_pullback`, `graphStalkLocalEquiv_fiberGerm`. It computes the contact of
the graph with a **horizontal** fibre `y = b`, and in characteristic `p` that length is `p`.

The rows `B · a` and `F̃ · a` need the **first**-coordinate mirror: the contact of the graph with a
**vertical** fibre `x = c`. No part of it exists — `affineGraph_firstProjection`, `firstChartMorphism`,
`polynomialGraphChart_firstProjection` and a vertical germ are all absent from the accepted tree and from
every lane. This module supplies exactly that mirror, and nothing else.

The mirror is cheap for one reason worth recording: `affineGraphMorphism p` is
`pullback.lift (parameterMorphism 1) (parameterMorphism p)`, so its **first** coordinate is
`parameterMorphism 1` — independent of `p`. The pulled-back vertical equation is therefore
`parameterMap 1 (fiberEquation c) = X₀ − C c`, the parameter itself, by the accepted
`pulledFiberEquation_eq`, which sits **outside** that file's `PositiveCharacteristic` section. So the whole
development here is **characteristic-free and primality-free**: the vertical ruling cuts the graph in a
uniformizer, at every `p`, including `p = 0`. Characteristic enters the horizontal case only, through
`pulledFiberEquation_eq_pow`.

* `pulledVerticalEquation`, `pulledVerticalEquation_eq` — the pullback is `X₀ − C c`;
* `localPulledVerticalEquation`, **`localPulledVerticalEquation_eq`** — in `k[t]_(t−c)` it is the
  accepted `localParameter c`;
* `affineGraph_firstProjection`, `firstChartRingMap`, `firstChartMorphism`,
  **`polynomialGraphChart_firstProjection`** — the morphism-level chart join for the first coordinate,
  the mirror of the accepted second-coordinate one;
* `graphVerticalGerm`, `graphVerticalGerm_stalkMap`, **`graphVerticalGerm_pullback`** — the germ, and the
  honest identification through the actual chart ring map (not through the stalk equivalence);
* **`graphStalkLocalEquiv_verticalGerm`** — the stalk equivalence carries it to `localParameter c`;
* **`graphStalk_vertical_contact_length`** — hence quotient length `1`.

**Not proved here.** This is the germ identification on the **graph scheme** `graph p` and its polynomial
chart. The rows need it for the restricted coefficient of the actual divisor `stageVerticalDivisor` on the
prime curve `B`, which additionally requires the `PrimeCurveInclusionLift` isomorphism
`C.toScheme ≅ strictTransform`, the tower transport, the translation `(τ_c × τ_0).inv`, and the chart-open
bookkeeping. Those are separate legs and are not attempted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusGraphVerticalContact

open KltDP.Geometry ProjectiveChart
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusGraphClosed
open FrobeniusGraphContact FrobeniusGraphStalkContact

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- **The first projection of the affine graph is the chart of `parameterMap 1`** — independent of
`p`, since `affineGraphMorphism p = pullback.lift (parameterMorphism 1) (parameterMorphism p)`. The
mirror of the accepted `affineGraph_secondProjection`. -/
theorem affineGraph_firstProjection (p : ℕ) :
    affineGraphMorphism (k := k) p ≫
        pullback.fst (projectiveSpaceToSpec k 1) (projectiveSpaceToSpec k 1) =
      Spec.map (CommRingCat.ofHom (parameterMap 1)) ≫ chartMorphism k 1 :=
  pullback.lift_fst _ _ _

/-- The equation of the **vertical** fibre `x = c`, pulled back along the graph's first coordinate. -/
def pulledVerticalEquation (c : k) : affineRing k 1 :=
  parameterMap 1 (fiberEquation c)

/-- **It is the parameter `t − c`.** Characteristic-free: the exponent is `1`. -/
theorem pulledVerticalEquation_eq (c : k) :
    pulledVerticalEquation (k := k) c = MvPolynomial.X 0 - MvPolynomial.C c := by
  simp only [pulledVerticalEquation, fiberEquation, map_sub, parameterMap_ratio,
    parameterMap_constants, pow_one]

/-- In polynomial coordinates it is `X - C c`. -/
theorem parameterPolynomialEquiv_pulledVerticalEquation (c : k) :
    parameterPolynomialEquiv (pulledVerticalEquation (k := k) c) =
      Polynomial.X - Polynomial.C c := by
  rw [pulledVerticalEquation_eq, map_sub, parameterPolynomialEquiv_X, parameterPolynomialEquiv_C]

/-- The pulled vertical equation in the local ring at `t = c`. -/
def localPulledVerticalEquation (c : k) : parameterLocalRing c :=
  algebraMap (Polynomial k) (parameterLocalRing c)
    (parameterPolynomialEquiv (pulledVerticalEquation c))

/-- **It is exactly the accepted `localParameter c`** — a uniformizer, with no characteristic
hypothesis anywhere. -/
theorem localPulledVerticalEquation_eq (c : k) :
    localPulledVerticalEquation (k := k) c = localParameter c := by
  rw [localPulledVerticalEquation, parameterPolynomialEquiv_pulledVerticalEquation]
  all_goals rfl

/-- The first-coordinate chart ring map in polynomial parameter coordinates: the mirror of the
accepted `secondChartRingMap`, with `parameterMap 1` in place of `parameterMap p`. -/
def firstChartRingMap : chartRing k 1 →+* Polynomial k :=
  parameterPolynomialEquiv.toRingHom.comp (parameterMap 1)

def firstChartMorphism :
    Spec (CommRingCat.of (Polynomial k)) ⟶ Spec (CommRingCat.of (chartRing k 1)) :=
  Spec.map (CommRingCat.ofHom (firstChartRingMap (k := k)))

/-- **This chart morphism is the first projection of the graph inclusion.** The mirror of the
accepted `polynomialGraphChart_secondProjection`. -/
theorem polynomialGraphChart_firstProjection (p : ℕ) :
    (polynomialGraphChart (k := k) p ≫ graphι p) ≫ firstProjection =
      firstChartMorphism ≫ chartMorphism k 1 := by
  rw [polynomialGraphChart_inclusion, Category.assoc, affineGraph_firstProjection,
    ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The vertical germ on the graph, named from the ring element through the chart — the same shape as
the accepted `graphFiberGerm`. -/
def graphVerticalGerm (p : ℕ) (c : k) : (graph (k := k) p).presheaf.stalk (pointOnGraph p c) :=
  (graphChartStalkEquiv p c).symm
    (StructureSheaf.toStalk (Polynomial k) (parameterSchemePoint c)
      (parameterPolynomialEquiv (pulledVerticalEquation c)))

theorem graphVerticalGerm_stalkMap (p : ℕ) (c : k) :
    (polynomialGraphChart p).stalkMap (parameterSchemePoint c) (graphVerticalGerm (k := k) p c) =
      StructureSheaf.toStalk (Polynomial k) (parameterSchemePoint c)
        (parameterPolynomialEquiv (pulledVerticalEquation c)) :=
  (graphChartStalkEquiv p c).apply_symm_apply _

/-- **The honest identification**: the germ is the stalk pullback of the vertical equation along the
actual first-coordinate chart ring map, not an element defined through the stalk equivalence. -/
theorem graphVerticalGerm_pullback (p : ℕ) (c : k) :
    (polynomialGraphChart p).stalkMap (parameterSchemePoint c) (graphVerticalGerm (k := k) p c) =
      (firstChartMorphism (k := k)).stalkMap (parameterSchemePoint c)
        (StructureSheaf.toStalk (chartRing k 1)
          ((firstChartMorphism (k := k)).base (parameterSchemePoint c)) (fiberEquation c)) := by
  rw [graphVerticalGerm_stalkMap]
  exact (AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom (firstChartRingMap (k := k)))
    (parameterSchemePoint c) (fiberEquation c)).symm

/-- **The stalk equivalence carries the vertical germ to the local parameter.** -/
theorem graphStalkLocalEquiv_verticalGerm (p : ℕ) (c : k) :
    graphStalkLocalEquiv p c (graphVerticalGerm (k := k) p c) = localParameter c := by
  have h : graphStalkLocalEquiv p c (graphVerticalGerm (k := k) p c) =
      localPulledVerticalEquation c := by
    change specStalkLocalizationEquiv (Polynomial k) (parameterSchemePoint c)
        (graphChartStalkEquiv p c ((graphChartStalkEquiv p c).symm
          (StructureSheaf.toStalk (Polynomial k) (parameterSchemePoint c)
            (parameterPolynomialEquiv (pulledVerticalEquation c))))) = _
    rw [RingEquiv.apply_symm_apply]
    exact StructureSheaf.stalkToFiberRingHom_toStalk (Polynomial k) (parameterSchemePoint c)
      (parameterPolynomialEquiv (pulledVerticalEquation c))
  rw [h, localPulledVerticalEquation_eq]

/-- **Vertical contact length one on the graph**, at every `p`, with no primality and no
characteristic hypothesis. -/
theorem graphStalk_vertical_contact_length (p : ℕ) (c : k) :
    Module.length ((graph (k := k) p).presheaf.stalk (pointOnGraph p c))
      ((graph (k := k) p).presheaf.stalk (pointOnGraph p c) ⧸
        Ideal.span {graphVerticalGerm (k := k) p c}) = 1 := by
  rw [quotient_span_length_eq_of_ringEquiv (graphStalkLocalEquiv p c),
    graphStalkLocalEquiv_verticalGerm, ← pow_one (localParameter c)]
  exact KltDP.RingTheory.dvr_length_quotient_uniformizer_pow (parameterLocalRing c)
    (localParameter c) (localParameter_uniformizer c) 1

end KltDP.Examples.FrobeniusGraphVerticalContact

namespace KltDP.Examples

open KltDP.Geometry ProjectiveChart
open FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusGraphContact
open FrobeniusGraphStalkContact FrobeniusGraphVerticalContact

/-- **F29: the vertical ruling fibre cuts the graph in a uniformizer.** The first-coordinate mirror of
the accepted horizontal contact development: the pulled-back equation of `x = c` is the local parameter
`t − c`, and the contact length is `1` — at every `p`, characteristic-free. -/
theorem f29_graph_vertical_contact (k : Type u) [Field k] (p : ℕ) (c : k) :
    graphStalkLocalEquiv p c (graphVerticalGerm (k := k) p c) = localParameter c ∧
    Module.length ((graph (k := k) p).presheaf.stalk (pointOnGraph p c))
      ((graph (k := k) p).presheaf.stalk (pointOnGraph p c) ⧸
        Ideal.span {graphVerticalGerm (k := k) p c}) = 1 :=
  ⟨graphStalkLocalEquiv_verticalGerm p c, graphStalk_vertical_contact_length p c⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_graph_vertical_contact_universe_check (k : Type u) [Field k] (p : ℕ) (c : k) :
    True := by
  have _ := f29_graph_vertical_contact.{u} k p c
  trivial

end KltDP.Examples
