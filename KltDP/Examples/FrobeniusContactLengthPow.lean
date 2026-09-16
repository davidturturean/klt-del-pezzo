import KltDP.Examples.FrobeniusVerticalContactStalk

/-!
# Contact length at an arbitrary exponent, and the graph contact length `p` (BRIEF27, item 2)

Lane A2's queued `crossing_contact_length` proves length `1` by rewriting along `crossingStalkEquiv`
and applying the accepted `dvr_length_quotient_uniformizer_pow` at exponent `1`. That accepted lemma
takes an **arbitrary** exponent, so the same proof gives the length at any exponent, and the
characteristic-`p` graph contact length is then a corollary of the accepted
`localPulledFiberEquation_eq_pow : localPulledFiberEquation p a = localParameter a ^ p`.

* **`crossing_contact_length_pow`, `fiber_crossing_contact_length_pow`**: a germ corresponding to
  `localParameter c ^ e` has quotient length `e`, along `B` and along `F̃`, at every stage. No
  primality and no characteristic hypothesis: this is pure discrete-valuation-ring arithmetic.
* **`crossing_graph_contact_length`**: under `[Fact p.Prime] [CharP k p]`, a germ corresponding to the
  accepted `localPulledFiberEquation p c` has quotient length `p` — the stage-level form of the
  accepted `FrobeniusGraphStalkContact.graphStalk_contact_length`, transported to `B` through the
  stalk identification rather than reproved.

The characteristic hypothesis enters only through `localPulledFiberEquation_eq_pow`, i.e. only to know
that the pulled-back fibre equation *is* a pure `p`-th power (`t^p − 1 = (t − 1)^p`); the length
statement itself is characteristic-free, as recorded for the vertical case.

Both `B` and `F̃` reuse the design point of the queued module: everything is indexed by
`lineParamPoint c` and the stalks are compared through the isomorphism's `inv`, so the two stalk
indices agree definitionally and no transport along an equality of points is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactLengthPow

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGraphContact FrobeniusGraphStalkContact
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform FrobeniusFiberClosure
open FrobeniusVerticalContactStalk

variable {k : Type u} [Field k]

/-- **Contact length at an arbitrary exponent along `B`**, characteristic-free. -/
theorem crossing_contact_length_pow (n m : ℕ) (c : k) (e : ℕ)
    (f : (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
    (hf : crossingStalkEquiv n m c f = localParameter c ^ e) :
    Module.length ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
      ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) ⧸
        Ideal.span {f}) = e := by
  rw [quotient_span_length_eq_of_ringEquiv (crossingStalkEquiv n m c) f, hf]
  exact KltDP.RingTheory.dvr_length_quotient_uniformizer_pow (parameterLocalRing c)
    (localParameter c) (localParameter_uniformizer c) e

/-- **Contact length at an arbitrary exponent along `F̃`**, characteristic-free. -/
theorem fiber_crossing_contact_length_pow (n : ℕ) (c : k) (e : ℕ)
    (f : (liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
      (fiberCrossingPoint n c))
    (hf : fiberCrossingStalkEquiv n c f = localParameter c ^ e) :
    Module.length
      ((liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
        (fiberCrossingPoint n c))
      ((liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
        (fiberCrossingPoint n c) ⧸ Ideal.span {f}) = e := by
  rw [quotient_span_length_eq_of_ringEquiv (fiberCrossingStalkEquiv n c) f, hf]
  exact KltDP.RingTheory.dvr_length_quotient_uniformizer_pow (parameterLocalRing c)
    (localParameter c) (localParameter_uniformizer c) e

/-- **The stage-level graph contact length `p`**: under `[Fact p.Prime] [CharP k p]`, a germ on `B`
corresponding to the accepted pulled-back fibre equation has quotient length `p`. -/
theorem crossing_graph_contact_length (p : ℕ) [Fact p.Prime] [CharP k p] (n m : ℕ) (c : k)
    (f : (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
    (hf : crossingStalkEquiv n m c f = localPulledFiberEquation p c) :
    Module.length ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
      ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) ⧸
        Ideal.span {f}) = p := by
  refine crossing_contact_length_pow n m c p f ?_
  rw [hf, localPulledFiberEquation_eq_pow]

end KltDP.Examples.FrobeniusContactLengthPow

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGraphContact FrobeniusGlobalBlowupStages
  FrobeniusGlobalStrictTransform FrobeniusFiberClosure FrobeniusVerticalContactStalk
  FrobeniusContactLengthPow

/-- **F29: contact lengths at every exponent, and the graph contact length `p`.** -/
theorem f29_contact_length_pow (k : Type u) [Field k] (n m : ℕ) (c : k) (e : ℕ)
    (f : (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
    (hf : crossingStalkEquiv n m c f = localParameter c ^ e)
    (g : (liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
      (fiberCrossingPoint n c))
    (hg : fiberCrossingStalkEquiv n c g = localParameter c ^ e) :
    Module.length ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
        ((strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c) ⧸
          Ideal.span {f}) = e ∧
    Module.length
        ((liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
          (fiberCrossingPoint n c))
        ((liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
          (fiberCrossingPoint n c) ⧸ Ideal.span {g}) = e :=
  ⟨crossing_contact_length_pow n m c e f hf, fiber_crossing_contact_length_pow n c e g hg⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_contact_length_pow_universe_check (k : Type u) [Field k] (n m : ℕ) (c : k) (e : ℕ)
    (f : (strictTransform (k := k) n (m + n)).presheaf.stalk (crossingPoint n m c))
    (hf : crossingStalkEquiv n m c f = localParameter c ^ e)
    (g : (liftedFiberClosure (projectiveProductInitial (k := k)) n).presheaf.stalk
      (fiberCrossingPoint n c))
    (hg : fiberCrossingStalkEquiv n c g = localParameter c ^ e) : True := by
  have _ := f29_contact_length_pow.{u} k n m c e f hf g hg
  trivial

end KltDP.Examples
