import Mathlib.Logic.Basic

/-!
# A single packaged choice for a proved refined-factor witness

Both choices are exactly the original nested Classical.choose operations.
Their carrier and proof projections are checked with abstract types once.
-/

noncomputable section

namespace KltDP.Geometry.RefinedFactorWitnessChoice

universe u v

variable {A : Type u} {P : A → Prop} {B : A → Type v} {Q : ∀ a, B a → Prop}

def select (h : ∃ a, P a ∧ ∃ b, Q a b) : Σ a, {b : B a // P a ∧ Q a b} :=
  ⟨Classical.choose h,
    ⟨Classical.choose (Classical.choose_spec h).2,
      (Classical.choose_spec h).1, Classical.choose_spec (Classical.choose_spec h).2⟩⟩

theorem select_fst (h : ∃ a, P a ∧ ∃ b, Q a b) :
    (select h).1 = Classical.choose h := rfl

theorem select_snd (h : ∃ a, P a ∧ ∃ b, Q a b) :
    (select h).2.val = Classical.choose (Classical.choose_spec h).2 := rfl

end KltDP.Geometry.RefinedFactorWitnessChoice
