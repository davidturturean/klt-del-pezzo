import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic.Abel

/-!
# The original ring of a union of two closed pieces

For arbitrary ideals I and J, functions on A/(I ∩ J) are exactly pairs of
functions on A/I and A/J agreeing on A/(I + J). No comaximality hypothesis
is imposed. In particular the result applies at the intersection of two
branches, where the ordinary Chinese remainder product is not appropriate.

The equalizer is Mathlib's original ring-homomorphism equalizer, and all
maps are the original quotient maps. A scheme/sheaf comparison is not part
of this algebraic statement.
-/

noncomputable section

namespace KltDP.Geometry.RationalTreePicard

variable (A : Type*) [CommRing A] (I J : Ideal A)

/-- Pairs of original quotient functions agreeing on the closed intersection. -/
def closedUnionRing : Subring ((A ⧸ I) × (A ⧸ J)) :=
  RingHom.eqLocus
    ((Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left)).comp
      (RingHom.fst (A ⧸ I) (A ⧸ J)))
    ((Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right)).comp
      (RingHom.snd (A ⧸ I) (A ⧸ J)))

/-- A pair with equal images on the intersection has an actual common lift
in the original ring. The two ideals need not be comaximal. -/
theorem exists_common_quotient_lift (a : A ⧸ I) (b : A ⧸ J)
    (h : Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left) a =
      Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right) b) :
    ∃ x : A, Ideal.Quotient.mk I x = a ∧ Ideal.Quotient.mk J x = b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  change Ideal.Quotient.mk (I ⊔ J) a = Ideal.Quotient.mk (I ⊔ J) b at h
  have hab : a - b ∈ I ⊔ J := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hab
  refine ⟨a - i, ?_, ?_⟩
  · apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    have he : a - i - a = -i := by abel
    rw [he]
    exact I.neg_mem hi
  · apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    have he : a - i - b = j := by
      calc
        a - i - b = (a - b) - i := by abel
        _ = j := by rw [← hij]; abel
    rw [he]
    exact hj

/-- The quotient by the ideal intersection maps to the original matching
pair ring using its two original quotient factors. -/
def closedUnionMap : (A ⧸ I ⊓ J) →+* closedUnionRing A I J where
  toFun x := ⟨(Ideal.Quotient.factor (show I ⊓ J ≤ I from inf_le_left) x,
    Ideal.Quotient.factor (show I ⊓ J ≤ J from inf_le_right) x), by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl⟩
  map_zero' := by apply Subtype.ext; exact Prod.ext (map_zero _) (map_zero _)
  map_one' := by apply Subtype.ext; exact Prod.ext (map_one _) (map_one _)
  map_add' x y := by apply Subtype.ext; exact Prod.ext (map_add _ x y) (map_add _ x y)
  map_mul' x y := by apply Subtype.ext; exact Prod.ext (map_mul _ x y) (map_mul _ x y)

theorem closedUnionMap_injective : Function.Injective (closedUnionMap A I J) := by
  intro x y h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  constructor
  · exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      (congrArg (fun z : closedUnionRing A I J => z.val.1) h)
  · exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      (congrArg (fun z : closedUnionRing A I J => z.val.2) h)

theorem closedUnionMap_surjective : Function.Surjective (closedUnionMap A I J) := by
  intro z
  obtain ⟨x, hx, hy⟩ := exists_common_quotient_lift A I J z.val.1 z.val.2 z.property
  refine ⟨Ideal.Quotient.mk (I ⊓ J) x, ?_⟩
  apply Subtype.ext
  exact Prod.ext hx hy

/-- The original union quotient is isomorphic to the branch-matching ring,
including when the two closed pieces meet. -/
def closedUnionRingEquiv : (A ⧸ I ⊓ J) ≃+* closedUnionRing A I J :=
  RingEquiv.ofBijective (closedUnionMap A I J)
    ⟨closedUnionMap_injective A I J, closedUnionMap_surjective A I J⟩

end KltDP.Geometry.RationalTreePicard
