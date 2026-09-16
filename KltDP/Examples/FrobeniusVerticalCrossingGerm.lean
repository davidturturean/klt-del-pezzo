import KltDP.Examples.FrobeniusVerticalSectionTransfer
import KltDP.Examples.FrobeniusVerticalChartBookkeeping
import KltDP.Examples.FrobeniusVerticalContactStalk
import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts
import KltDP.Geometry.AffineRegularLocus

/-!
# Leg 3c(iii): the product germ of the vertical divisor is the local parameter (BRIEF52)

Legs 1, 2, 3a, 3b and 3c(i)(ii) reduced the rows to one statement: identify the **product** germ that
`towerStalkEquiv_stageVerticalChartZero` reduces to — the germ of
`(verticalTranslation c).inv.app (productOpen 0 0) (verticalZeroChartEquation 0)`, the coefficient of
the divisor `x = c` on its own chart — with the accepted `localParameter c`.

The two live in different rings, and the statement only typechecks once that is faced: the product's
stalk at the crossing point is two-dimensional, while `localParameter c` lives in the one-dimensional
`parameterLocalRing c`. **The germ must therefore be pulled back to the parameter line first**, along
the graph parameterisation `projectiveGraphMorphism p`, whose stalk map lands exactly in
`(projectiveSpace k 1).presheaf.stalk (lineParamPoint c)` — the ring `lineStalkLocalEquiv c`
identifies with `parameterLocalRing c`. That is what this module proves.

## The route, and why it is not the one the handover sketched

The handover proposed taking `.app` of the translated chart join through `Scheme.comp_app`. That is
avoidable, and avoiding it is what keeps the proof cast-free: **`.app` is never computed**. Instead

* `Scheme.stalkMap_germ_apply`, used **backwards**, turns the germ of the *translated* section on the
  *translated* open into `(verticalTranslation c).inv.stalkMap` applied to the germ of the plain
  section `verticalZeroChartEquation 0` on the plain chart open `productOpen 0 0`. No section is
  transported across a morphism equality and no open is rewritten;
* the three stalk maps then compose into the single morphism
  `(polynomialLineChart ≫ projectiveGraphMorphism p) ≫ (verticalTranslation c).inv`, which
  **factors through the vertical chart** (`translatedGraphParametrisation`);
* on a morphism that so factors, a generic lemma computes the whole germ at ring level.

`specStalkLocalizationEquiv_stalkMap_germ` is that generic lemma, and it is stated with the morphism
`F` as a **variable** together with `hF : F = Spec.map (ofHom φ) ≫ j`, so that `subst` eliminates the
factorisation before any germ index has to move. This is the general answer to the point-index trap:
a propositional identification of morphisms may be consumed by `subst` at a variable, where it costs
nothing, instead of by transport at a concrete term, where it costs a cast.

## The hinge that had to be found

`curveInPlane_diagonalChart` (accepted) states the graph parameterisation in terms of
`ProjectiveLineComparison.polynomialChartMap k 0`, whereas the whole germ development — `localParameter`,
`lineStalkLocalEquiv`, `lineParamPoint`, `parameterSchemePoint` — is phrased with
`FrobeniusGraphStalkContact.polynomialLineChart`. **No lemma related the two**, in the accepted tree or
in any lane, and every route to the rows needs one, because `planeChart` is itself built from
`polynomialChartMap k 0`. They are in fact the *same morphism*: both are `Proj.awayι` at `X 0`
precomposed with `Spec.map` of the same coordinate identification, since `parameterPolynomialEquiv`
and `oneVariablePolynomialEquiv` differ only in `finOneEquiv` versus `Equiv.equivPUnit (Fin 1)` — and
`finOneEquiv` is *defined* as `Equiv.equivPUnit _`. Hence `polynomialLineChart_eq_polynomialChartMap`
is `rfl`.

## What is proved

* `stalkMap_germ_chartSections` — generic: an affine chart's stalk map carries the germ of a section of
  the chart open to `StructureSheaf.toStalk` of the corresponding ring element;
* `specStalkLocalizationEquiv_stalkMap_germ` — generic: the germ of a chart section pulled back along a
  morphism factoring through that chart, computed at ring level;
* `polynomialLineChart_eq_polynomialChartMap` — the hinge;
* `translatedGraphRingMap`, `translatedGraphRingMap_uCoord` — the ring map `u ↦ t − c`, `v ↦ t^p` of the
  translated graph parameterisation, and its value on the vertical coordinate, which is Leg 2's
  identity read through the first coordinate;
* `translatedGraphParametrisation` — that parameterisation factors the translated graph through the
  vertical chart;
* `graphParamPoint_mem_translatedOpen` — the crossing point lies in the divisor's chart open;
* **`lineStalkLocalEquiv_translatedVerticalGerm`** — the germ of the divisor's chart coefficient, pulled
  back to the parameter line along the graph, is `localParameter c`.

Characteristic-free and primality-free, every `p` and every `c`, `c = 0` included: `c ≠ 0` is needed
only from Leg 3b onward, and Leg 3b is not consumed here.

**Not proved here, and no row is claimed.** Two things still separate this from `B · a`, `B · b` and
`F̃ · a`, and both are real:

1. **The point index.** Leg 3b's `towerStalkEquiv_stageVerticalChartZero` indexes the same germ by
   `(projectiveContactProjection (n+1)).base (stageCrossingPoint n m c)`, which is only
   *propositionally* equal to `(projectiveGraphMorphism (m+(n+1))).base (lineParamPoint c)` used here
   (by `verticalCrossingPoint_toInitial`). Under the standing rule the fix is to **re-index**, not to
   transport a stalk along the point equality.
2. **The restriction to the curve.** The rows consume a germ on `B_n`, obtained from the stage germ
   through `strictTransformι.stalkMap`, and `crossingStalkEquiv` is the composite of
   `graphStrictIsoProjectiveLine.inv.stalkMap` with `lineStalkLocalEquiv`. Relating that composite to
   `projectiveGraphMorphism`'s stalk map is a further morphism identity
   (`graphStrictIsoProjectiveLine_hom_comp`), not yet taken.

Claiming the rows from this module alone would be the convenient reading, not the true one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalCrossingGerm

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusProductPlaneChart FrobeniusTranslatedCharts
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusGraphPicardClassPowerCharts
open FrobeniusGraphContact FrobeniusGraphStalkContact
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusVerticalTranslationEquation FrobeniusVerticalSectionTransfer
open FrobeniusVerticalChartBookkeeping
open FrobeniusVerticalContactLength FrobeniusVerticalContactStalk

section Generic

variable {R S : Type u} [CommRing R] [CommRing S] {Y : Scheme.{u}}

/-- **An affine chart's stalk map sends the germ of a chart section to `toStalk` of its ring element.**
This is the ring-level content of the accepted `openImmersionStalkLocalizationEquiv_germ`, isolated
before the localization comparison so that it can be composed with further stalk maps. -/
theorem stalkMap_germ_chartSections (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j]
    (p : PrimeSpectrum R) (s : Γ(Y, j ''ᵁ ⊤)) :
    j.stalkMap p (Y.presheaf.germ (j ''ᵁ ⊤) (j.base p) (mem_chart_image_top j p) s) =
      StructureSheaf.toStalk R p (chartSectionsEquiv j s) := by
  apply (specStalkLocalizationEquiv R p).injective
  have h2 : specStalkLocalizationEquiv R p
        (StructureSheaf.toStalk R p (chartSectionsEquiv j s)) =
      algebraMap R (Localization.AtPrime p.asIdeal) (chartSectionsEquiv j s) :=
    StructureSheaf.stalkToFiberRingHom_toStalk R p (chartSectionsEquiv j s)
  rw [h2]
  exact openImmersionStalkLocalizationEquiv_germ j p s

/-- **The germ of a chart section, pulled back along a morphism that factors through the chart.**

`F` is a variable and the factorisation `hF` is eliminated by `subst`, so the point index
`F.base q` never has to be transported: the propositional identification of morphisms is consumed
where it is free. -/
theorem specStalkLocalizationEquiv_stalkMap_germ
    (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j] (φ : R →+* S)
    (q : PrimeSpectrum S) (F : Spec (CommRingCat.of S) ⟶ Y)
    (hF : F = Spec.map (CommRingCat.ofHom φ) ≫ j)
    (hq : F.base q ∈ j ''ᵁ ⊤) (s : Γ(Y, j ''ᵁ ⊤)) :
    specStalkLocalizationEquiv S q
        (F.stalkMap q (Y.presheaf.germ (j ''ᵁ ⊤) (F.base q) hq s)) =
      algebraMap S (Localization.AtPrime q.asIdeal) (φ (chartSectionsEquiv j s)) := by
  subst hF
  have hcomp : (Spec.map (CommRingCat.ofHom φ) ≫ j).stalkMap q
        (Y.presheaf.germ (j ''ᵁ ⊤)
          ((Spec.map (CommRingCat.ofHom φ) ≫ j).base q) hq s) =
      StructureSheaf.toStalk S q (φ (chartSectionsEquiv j s)) := by
    rw [Scheme.stalkMap_comp, CommRingCat.comp_apply]
    show (Spec.map (CommRingCat.ofHom φ)).stalkMap q
        (j.stalkMap ((Spec.map (CommRingCat.ofHom φ)).base q)
          (Y.presheaf.germ (j ''ᵁ ⊤) (j.base ((Spec.map (CommRingCat.ofHom φ)).base q))
            (mem_chart_image_top j ((Spec.map (CommRingCat.ofHom φ)).base q)) s)) = _
    rw [stalkMap_germ_chartSections]
    exact AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom φ) q (chartSectionsEquiv j s)
  rw [hcomp]
  exact StructureSheaf.stalkToFiberRingHom_toStalk S q (φ (chartSectionsEquiv j s))

end Generic

variable {k : Type u} [Field k]

/-- **The hinge: the germ development's polynomial chart of `P¹` is the accepted polynomial chart map.**
Both are `Proj.awayι` at `X 0` precomposed with `Spec.map` of the same coordinate identification:
`parameterPolynomialEquiv` and `oneVariablePolynomialEquiv` differ only in `finOneEquiv` versus
`Equiv.equivPUnit (Fin 1)`, and `finOneEquiv` is defined as the latter. No lemma relating them existed
in the accepted tree or in any lane, and every route from the divisor to `localParameter` needs one. -/
theorem polynomialLineChart_eq_polynomialChartMap :
    polynomialLineChart (k := k) = ProjectiveLineComparison.polynomialChartMap k 0 := rfl

/-- The coordinate ring map of the **translated** graph parameterisation: `u ↦ t − c`, `v ↦ t^p`. -/
def translatedGraphRingMap (p : ℕ) (c : k) : planeRing k →+* Polynomial k :=
  (Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k)).comp
    (coordinateTranslation (-c) (-(0 : k))).toRingHom

/-- **Its value on the vertical coordinate is the parameter equation of the point `c`.** This is
Leg 2's ring identity read through the first coordinate: the translate of `u` is the image of
`X − C c`, and the graph parameterisation restricts the first coordinate to the parameter. -/
theorem translatedGraphRingMap_uCoord (p : ℕ) (c : k) :
    translatedGraphRingMap (k := k) p c uCoord = Polynomial.X - Polynomial.C c := by
  change Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k)
    (coordinateTranslation (-c) (-(0 : k)) (uCoord (k := k))) = _
  rw [coordinateTranslation_uCoord_eq_firstCoordinateMap]
  show Polynomial.eval (Polynomial.X ^ p : Polynomial k)
    (Polynomial.C (Polynomial.X - Polynomial.C c)) = _
  exact Polynomial.eval_C

/-- **The translated graph parameterisation factors through the vertical chart.** The graph, moved by
the inverse vertical translation, is the image of `Spec` of `translatedGraphRingMap` under
`productChart 0 0`. Every step is at morphism level; no section and no open is moved. -/
theorem translatedGraphParametrisation (p : ℕ) (c : k) :
    Spec.map (CommRingCat.ofHom (translatedGraphRingMap (k := k) p c)) ≫ productChart 0 0 =
      (polynomialLineChart (k := k) ≫ projectiveGraphMorphism p) ≫
        (verticalTranslation (k := k) c).inv := by
  have hsplit : Spec.map (CommRingCat.ofHom (translatedGraphRingMap (k := k) p c)) =
      curveInPlane p ≫ (planeTranslationIso (-c) (-(0 : k))).hom := by
    change Spec.map (CommRingCat.ofHom
        ((Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k)).comp
          (coordinateTranslation (-c) (-(0 : k))).toRingHom)) =
      Spec.map (CommRingCat.ofHom
          (Polynomial.evalRingHom (Polynomial.X ^ p : Polynomial k))) ≫
        Spec.map (CommRingCat.ofHom (coordinateTranslation (-c) (-(0 : k))).toRingHom)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hsplit, Category.assoc, ← productChart_verticalTranslation, ← Category.assoc,
    curveInPlane_diagonalChart, polynomialLineChart_eq_polynomialChartMap]

/-- **The crossing point lies in the divisor's chart open.** The graph parameterisation sends the
parameter point `t = c` to the graph point `(c, c^p)`, which the inverse translation carries into
`productOpen 0 0` by Leg 3a. Every step is point-level, inside a `Prop`. -/
theorem graphParamPoint_mem_translatedOpen (p : ℕ) (c : k) :
    (projectiveGraphMorphism (k := k) p).base (lineParamPoint c) ∈
      (verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0 := by
  show (verticalTranslation (k := k) c).inv.base
      ((projectiveGraphMorphism (k := k) p).base
        ((polynomialLineChart (k := k)).base (parameterSchemePoint c))) ∈
    productOpen (k := k) 0 0
  rw [polynomialLineChart_point, graphMorphism_base_point]
  exact translatedCrossingPoint_mem_productOpen p c

/-- **Leg 3c(iii): the product germ of the vertical divisor's chart coefficient, pulled back to the
parameter line along the graph, is the accepted `localParameter c`.**

The germ is of the actual coefficient the divisor `x = c` carries on its own chart — the translate
`(verticalTranslation c).inv.app _ (verticalZeroChartEquation 0)` — taken at the crossing point of the
graph with that fibre. Nothing here is true by construction: the section exists first and its germ is
computed, through the chart ring map, exactly as the accepted `graphFiberGerm_pullback` does. -/
theorem lineStalkLocalEquiv_translatedVerticalGerm (p : ℕ) (c : k) :
    lineStalkLocalEquiv c
        ((projectiveGraphMorphism (k := k) p).stalkMap (lineParamPoint c)
          ((projectiveProduct k).presheaf.germ
            ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
            ((projectiveGraphMorphism (k := k) p).base (lineParamPoint c))
            (graphParamPoint_mem_translatedOpen p c)
            ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
              (verticalZeroChartEquation 0)))) =
      localParameter c := by
  have hkey := specStalkLocalizationEquiv_stalkMap_germ (productChart (k := k) 0 0)
    (translatedGraphRingMap (k := k) p c) (parameterSchemePoint c)
    ((polynomialLineChart (k := k) ≫ projectiveGraphMorphism p) ≫
      (verticalTranslation (k := k) c).inv)
    (translatedGraphParametrisation p c).symm
    (graphParamPoint_mem_translatedOpen p c)
    (verticalZeroChartEquation 0)
  rw [chartSectionsEquiv_verticalZeroChartEquation, translatedGraphRingMap_uCoord] at hkey
  rw [Scheme.stalkMap_comp, CommRingCat.comp_apply, Scheme.stalkMap_comp,
    CommRingCat.comp_apply] at hkey
  rw [← Scheme.stalkMap_germ_apply]
  exact hkey

end KltDP.Examples.FrobeniusVerticalCrossingGerm

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusGraphContact FrobeniusGraphStalkContact
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusVerticalContactLength FrobeniusVerticalContactStalk
open FrobeniusVerticalCrossingGerm

/-- **F29: the vertical fibre's divisor germ at the crossing point of `B` is the local parameter.**
The coefficient the divisor `x = c` actually carries on its chart, germinated at the crossing point
and pulled back to the parameter line along the graph, is `localParameter c` — a uniformizer.
Characteristic-free and primality-free, every `p` and every `c`. -/
theorem f29_vertical_crossing_germ (k : Type u) [Field k] (p : ℕ) (c : k) :
    lineStalkLocalEquiv c
        ((projectiveGraphMorphism (k := k) p).stalkMap (lineParamPoint c)
          ((projectiveProduct k).presheaf.germ
            ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
            ((projectiveGraphMorphism (k := k) p).base (lineParamPoint c))
            (graphParamPoint_mem_translatedOpen p c)
            ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
              (verticalZeroChartEquation 0)))) =
      localParameter c :=
  lineStalkLocalEquiv_translatedVerticalGerm p c

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_crossing_germ_universe_check (k : Type u) [Field k] (p : ℕ) (c : k) :
    True := by
  have _ := f29_vertical_crossing_germ.{u} k p c
  trivial

end KltDP.Examples
