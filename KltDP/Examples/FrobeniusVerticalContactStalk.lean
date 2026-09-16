import KltDP.Examples.FrobeniusVerticalContactLength
import KltDP.Geometry.RationalTreePicardRestrictStalk
import KltDP.Geometry.DivisorOrderLength

/-!
# Vertical contact length one along `B` and `F̃` (BRIEF26, item 2) — characteristic-free

The strict transforms are isomorphic to `P¹` (accepted `graphStrictIsoProjectiveLine`,
`fiberStrictIsoProjectiveLine`), and the stalk of `P¹` at the parameter point `t = c` is the accepted
`parameterLocalRing c` (lane A2's `lineStalkLocalEquiv`). Transporting the quotient length along that
identification and finishing with the accepted `dvr_length_quotient_uniformizer_pow` gives contact
length **one**, with no primality or characteristic hypothesis: the vertical ruling cuts the parameter
`t − c`, a uniformizer.

Everything is indexed by `lineParamPoint c = polynomialLineChart.base (parameterSchemePoint c)`, and the
stalk comparison uses the **inverse** of the isomorphism, so that both stalk indices agree
definitionally (`crossingPoint` is by definition `iso.inv.base (lineParamPoint c)`) and no transport of
a stalk along an equality of points is needed.

* `crossingPoint`, `fiberCrossingPoint`: the points of `B_n`, resp. `F̃_n`, over `t = c`;
* `crossingStalkEquiv`, `fiberCrossingStalkEquiv`: their stalks are `k[t]_(t-c)`;
* **`crossing_contact_length`, `fiber_crossing_contact_length`**: a germ corresponding to
  `localParameter c` has quotient length `1`.

The germ produced by an actual vertical divisor is identified with `localParameter c` through the
accepted chart join (`planeChart_fst` at morphism level, `polynomialChartMap_eq` by `rfl`, and the
coordinate transport `u − c ↦ X − C c`); that step and the rows are the next module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalContactStalk

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusProjectivePoints FrobeniusGraphContact FrobeniusGraphStalkContact
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform FrobeniusFiberClosure
open FrobeniusStrictTransformIsoProjectiveLine FrobeniusVerticalContactLength

variable {k : Type u} [Field k]

/-- The point `t = c` of `P¹`, indexed through the accepted polynomial chart. -/
abbrev lineParamPoint (c : k) : projectiveSpace k 1 :=
  (polynomialLineChart (k := k)).base (parameterSchemePoint c)

section Graph

variable (n m : ℕ)

/-- The point of `B_n` over `t = c`. -/
def crossingPoint (c : k) : strictTransform (k := k) n (m + n) :=
  (graphStrictIsoProjectiveLine (k := k) n m).inv.base (lineParamPoint c)

/-- **The stalk of `B_n` at that point is the accepted local ring `k[t]_(t-c)`.** -/
def crossingStalkEquiv (c : k) :
    (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) ≃+*
      parameterLocalRing c :=
  haveI : IsIso ((graphStrictIsoProjectiveLine (k := k) n m).inv.stalkMap (lineParamPoint c)) :=
    isIso_stalkMap_of_isIso _ _
  (asIso ((graphStrictIsoProjectiveLine (k := k) n m).inv.stalkMap
      (lineParamPoint c))).commRingCatIsoToRingEquiv.trans (lineStalkLocalEquiv c)

/-- **Vertical contact length one along `B`**, characteristic-free: a germ corresponding to the
uniformizer `t − c` has quotient length `1`. -/
theorem crossing_contact_length (c : k)
    (f : (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
    (hf : crossingStalkEquiv n m c f = localParameter c) :
    Module.length ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
      ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) ⧸
        Ideal.span {f}) = 1 := by
  rw [quotient_span_length_eq_of_ringEquiv (crossingStalkEquiv n m c) f, hf,
    ← pow_one (localParameter c)]
  exact KltDP.RingTheory.dvr_length_quotient_uniformizer_pow (parameterLocalRing c)
    (localParameter c) (localParameter_uniformizer c) 1

end Graph

section Fiber

variable (n : ℕ)

/-- The point of `F̃_n` over `t = c`. -/
def fiberCrossingPoint (c : k) :
    liftedFiberClosure (projectiveProductInitial (k := k)) n :=
  (fiberStrictIsoProjectiveLine (k := k) n).inv.base (lineParamPoint c)

/-- **The stalk of `F̃_n` at that point is `k[t]_(t-c)`.** -/
def fiberCrossingStalkEquiv (c : k) :
    (liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
        (fiberCrossingPoint n c) ≃+* parameterLocalRing c :=
  haveI : IsIso ((fiberStrictIsoProjectiveLine (k := k) n).inv.stalkMap (lineParamPoint c)) :=
    isIso_stalkMap_of_isIso _ _
  (asIso ((fiberStrictIsoProjectiveLine (k := k) n).inv.stalkMap
      (lineParamPoint c))).commRingCatIsoToRingEquiv.trans (lineStalkLocalEquiv c)

/-- **Vertical contact length one along `F̃`**, characteristic-free. -/
theorem fiber_crossing_contact_length (c : k)
    (f : (liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
      (fiberCrossingPoint n c))
    (hf : fiberCrossingStalkEquiv n c f = localParameter c) :
    Module.length
      ((liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
        (fiberCrossingPoint n c))
      ((liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
        (fiberCrossingPoint n c) ⧸ Ideal.span {f}) = 1 := by
  rw [quotient_span_length_eq_of_ringEquiv (fiberCrossingStalkEquiv n c) f, hf,
    ← pow_one (localParameter c)]
  exact KltDP.RingTheory.dvr_length_quotient_uniformizer_pow (parameterLocalRing c)
    (localParameter c) (localParameter_uniformizer c) 1

end Fiber

end KltDP.Examples.FrobeniusVerticalContactStalk

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGraphContact FrobeniusGlobalBlowupStages
  FrobeniusGlobalStrictTransform FrobeniusFiberClosure FrobeniusVerticalContactStalk

/-- **F29: vertical contact length one along `B` and along `F̃`**, at every stage, characteristic-free. -/
theorem f29_vertical_contact_length (k : Type u) [Field k] (n m : ℕ) (c : k)
    (f : (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
    (hf : crossingStalkEquiv n m c f = localParameter c)
    (g : (liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
      (fiberCrossingPoint n c))
    (hg : fiberCrossingStalkEquiv n c g = localParameter c) :
    Module.length ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
        ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) ⧸
          Ideal.span {f}) = 1 ∧
    Module.length
        ((liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
          (fiberCrossingPoint n c))
        ((liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
          (fiberCrossingPoint n c) ⧸ Ideal.span {g}) = 1 :=
  ⟨crossing_contact_length n m c f hf, fiber_crossing_contact_length n c g hg⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_vertical_contact_length_universe_check (k : Type u) [Field k] (n m : ℕ) (c : k)
    (f : (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
    (hf : crossingStalkEquiv n m c f = localParameter c)
    (g : (liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
      (fiberCrossingPoint n c))
    (hg : fiberCrossingStalkEquiv n c g = localParameter c) : True := by
  have _ := f29_vertical_contact_length.{u} k n m c f hf g hg
  trivial

end KltDP.Examples
