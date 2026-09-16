import KltDP.RingTheory.AssociatedGradedRees
import KltDP.RingTheory.LocalAdicOrder

/-!
# Leading forms, and additivity of the adic order from `gr` being a domain

BRIEF37 tasks 2 and 3. The leading form of `f` is its class in `gr_I R` in degree `adicOrder I f`; it is
nonzero exactly because `f` lies in `I ^ ord f` and not in `I ^ (ord f + 1)`. Additivity of the order
then follows from `gr` having no zero divisors, which closes the gap that
`KltDP.RingTheory.LocalAdicOrder.HasAdditiveAdicOrder` was left carrying.

## The argument

Superadditivity `ord f + ord g ≤ ord (f * g)` is unconditional and already proved. For the reverse,
suppose `ord (f*g) > a + b` where `a = ord f`, `b = ord g`. Then `f * g ∈ I ^ (a+b+1)`, so by
`ofPow_eq_zero_iff` the degree-`a+b` class of `f*g` vanishes; by `ofPow_mul` that class is the product
of the leading forms of `f` and `g`. In a domain one factor must vanish, contradicting
`leadingForm_ne_zero`. Nothing else is needed — in particular neither the direct-sum decomposition of
`gr` nor its grading.

## Why this discharges rather than assumes

`HasAdditiveAdicOrder` was introduced as a named `Prop` precisely because the hypothesis "the associated
graded ring is a domain" could not be stated at this pin. It now can be, so
`hasAdditiveAdicOrder_of_isDomain` **derives** the property instead of assuming it. For the intended
application `O_{S,x}` is regular local of dimension two, whose `gr` is a polynomial ring in two
variables over the residue field and hence a domain — but that theorem is explicitly out of scope for
this brief and is not attempted here; it is the one remaining input.

## The equivalence: one direction proved, one stated

`GrDomainIffLeadingFormsMultiply` records that `gr` being a domain is equivalent to multiplicativity of
leading forms. The **forward** direction is proved here (`leadingFormsMultiply_of_isDomain`): it is
`adicOrder_mul_of_isDomain` together with `ofPow_congr`, the transport of a degree-indexed class along
`ord (f*g) = ord f + ord g`. The **reverse** needs the grading on `gr` — that a nonzero product of
homogeneous elements detects a nonzero product in the ring — which is not built, so the equivalence
itself is only stated, as the brief allows.
-/

noncomputable section

open IsLocalRing

universe u

namespace KltDP.RingTheory.LeadingForm

open KltDP.RingTheory.AssociatedGradedRees
open KltDP.RingTheory.LocalAdicOrder

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ## The leading form -/

/-- **The leading form of `f`**: its class in `gr_I R`, in degree `adicOrder I f`. -/
def leadingForm (f : R) (hbdd : BddAbove (powMemSet I f)) : AssociatedGraded I :=
  ofPow I (adicOrder I f) ⟨f, mem_pow_adicOrder hbdd⟩

/-- **The leading form is nonzero.** This is exactly the characterisation of the order: `f` lies in
`I ^ ord f` but not in `I ^ (ord f + 1)`. -/
theorem leadingForm_ne_zero (f : R) (hbdd : BddAbove (powMemSet I f)) :
    leadingForm I f hbdd ≠ 0 := fun h =>
  not_mem_pow_succ hbdd ((ofPow_eq_zero_iff I _ _).mp h)

/-! ## Additivity from `gr` a domain -/

/-- **Additivity of the adic order**, from `gr_I R` having no zero divisors. -/
theorem adicOrder_mul_of_isDomain [IsDomain (AssociatedGraded I)] {f g : R}
    (hf : BddAbove (powMemSet I f)) (hg : BddAbove (powMemSet I g))
    (hfg : BddAbove (powMemSet I (f * g))) :
    adicOrder I (f * g) = adicOrder I f + adicOrder I g := by
  refine le_antisymm ?_ (add_le_adicOrder_mul hf hg hfg)
  by_contra hlt
  push_neg at hlt
  have hmem : f * g ∈ I ^ (adicOrder I f + adicOrder I g + 1) :=
    (le_adicOrder_iff_mem hfg _).mp hlt
  have hzero : ofPow I (adicOrder I f) ⟨f, mem_pow_adicOrder hf⟩
      * ofPow I (adicOrder I g) ⟨g, mem_pow_adicOrder hg⟩ = 0 := by
    rw [ofPow_mul]
    exact (ofPow_eq_zero_iff I _ _).mpr hmem
  rcases mul_eq_zero.mp hzero with h | h
  · exact leadingForm_ne_zero I f hf h
  · exact leadingForm_ne_zero I g hg h

/-- **The consumer.** `HasAdditiveAdicOrder` is now derived, not assumed, on a Noetherian domain at a
proper ideal whose associated graded ring is a domain. -/
theorem hasAdditiveAdicOrder_of_isDomain [IsNoetherianRing R] [IsDomain R]
    [IsDomain (AssociatedGraded I)] (hI : I ≠ ⊤) : HasAdditiveAdicOrder I := fun _ _ hf hg =>
  adicOrder_mul_of_isDomain I (bddAbove_powMemSet_of_isDomain hI hf)
    (bddAbove_powMemSet_of_isDomain hI hg)
    (bddAbove_powMemSet_of_isDomain hI (mul_ne_zero hf hg))

/-- **The closed-point form of the consumer**: multiplicity at a closed point is additive whenever the
associated graded ring of the maximal ideal is a domain. -/
theorem hasAdditiveAdicOrder_maximalIdeal [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsDomain (AssociatedGraded (maximalIdeal R))] :
    HasAdditiveAdicOrder (maximalIdeal R) := fun _ _ hf hg =>
  adicOrder_mul_of_isDomain (maximalIdeal R) (bddAbove_powMemSet_of_isLocalRing hf)
    (bddAbove_powMemSet_of_isLocalRing hg)
    (bddAbove_powMemSet_of_isLocalRing (mul_ne_zero hf hg))

/-! ## The equivalence, as a statement -/

/-- Leading forms multiply. -/
def LeadingFormsMultiply : Prop :=
  ∀ (f g : R) (hf : BddAbove (powMemSet I f)) (hg : BddAbove (powMemSet I g))
    (hfg : BddAbove (powMemSet I (f * g))),
    leadingForm I (f * g) hfg = leadingForm I f hf * leadingForm I g hg

/-- **The forward direction**: if `gr` is a domain then leading forms multiply. The content is that the
degree index moves, via `ofPow_congr`, along `ord (f*g) = ord f + ord g`. -/
theorem leadingFormsMultiply_of_isDomain [IsDomain (AssociatedGraded I)] :
    LeadingFormsMultiply I := by
  intro f g hf hg hfg
  have h1 : leadingForm I f hf * leadingForm I g hg
      = ofPow I (adicOrder I f + adicOrder I g)
          ⟨f * g, by
            rw [pow_add]
            exact Ideal.mul_mem_mul (mem_pow_adicOrder hf) (mem_pow_adicOrder hg)⟩ :=
    ofPow_mul I _ _ _ _
  rw [h1]
  exact ofPow_congr I (adicOrder_mul_of_isDomain I hf hg hfg) _ _ rfl

/-- **`gr` is a domain exactly when leading forms multiply.** The forward direction is proved above as
`leadingFormsMultiply_of_isDomain`; the reverse needs the grading on `gr`, which is not built, so the
equivalence itself is recorded as a statement per BRIEF37. -/
def GrDomainIffLeadingFormsMultiply : Prop :=
  IsDomain (AssociatedGraded I) ↔ LeadingFormsMultiply I

end KltDP.RingTheory.LeadingForm
