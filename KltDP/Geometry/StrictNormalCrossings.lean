import KltDP.Geometry.SingularPoints
import KltDP.Geometry.EffectiveCartierSection
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.BigOperators.Fin

/-!
# Strict normal crossings in the original local rings

The local definition uses a complete regular parameter system, of size the
actual Krull dimension, and distinct parameter factors. The unit case places
no regularity requirement off the divisor. This is the local definition of
Stacks 0BI9, with regular parameters as in 00KU. The global Cartier interface
here is restricted to integral locally Noetherian schemes. Rational divisor
coefficients are separate from this condition on the reduced support.
-/

noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

namespace KltDP.Geometry

/-- A complete regular parameter system in the original local ring. -/
def IsRegularParameterFamily (R : Type u) [CommRing R] [IsLocalRing R]
    (d : ℕ) (t : Fin d → R) : Prop :=
  RegularLocal R ∧
    ringKrullDim R = (d : WithBot ℕ∞) ∧
    Ideal.span (Set.range t) = maximalIdeal R

/-- A unit or a unit times distinct members of a complete regular parameter
system. The full system has the actual local dimension. -/
def IsStrictNormalCrossingsEquation (R : Type u) [CommRing R] [IsLocalRing R]
    (f : R) : Prop :=
  IsUnit f ∨
    ∃ (d : ℕ) (t : Fin d → R),
      IsRegularParameterFamily R d t ∧
      ∃ (r : ℕ) (_ : 0 < r) (hrd : r ≤ d) (v : Rˣ),
        f = (v : R) * ∏ i : Fin r, t (Fin.castLE hrd i)

namespace IsStrictNormalCrossingsEquation

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Changing a local equation by a unit preserves strict normal crossings. -/
theorem unit_mul {f : R} (hf : IsStrictNormalCrossingsEquation R f) (v : Rˣ) :
    IsStrictNormalCrossingsEquation R ((v : R) * f) := by
  rcases hf with hf | ⟨d, t, ht, r, hr, hrd, w, hw⟩
  · exact Or.inl (v.isUnit.mul hf)
  · refine Or.inr ⟨d, t, ht, r, hr, hrd, v * w, ?_⟩
    rw [hw, Units.val_mul, mul_assoc]

/-- A generator of a one-dimensional regular maximal ideal is an SNC equation. -/
theorem of_single_parameter (hR : RegularLocal R) (hdim : ringKrullDim R = 1)
    (f : R) (hf : Ideal.span {f} = maximalIdeal R) :
    IsStrictNormalCrossingsEquation R f := by
  refine Or.inr ⟨1, ![f], ⟨hR, ?_, ?_⟩, 1, Nat.zero_lt_succ 0, le_rfl, 1, ?_⟩
  · simpa using hdim
  · simpa only [Matrix.range_cons_empty] using hf
  · simp [Fin.prod_univ_one]

/-- The first member of an actual regular parameter pair is an SNC equation. -/
theorem of_first_parameter (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
    (f g : R) (hfg : Ideal.span {f, g} = maximalIdeal R) :
    IsStrictNormalCrossingsEquation R f := by
  refine Or.inr ⟨2, ![f, g], ⟨hR, ?_, ?_⟩, 1, Nat.zero_lt_succ 0,
    by decide, 1, ?_⟩
  · simpa using hdim
  · simpa only [Matrix.range_cons_cons_empty] using hfg
  · simp [Fin.prod_univ_one]

/-- A product of the two distinct members of a regular parameter pair is
the local equation of a strict crossing. -/
theorem of_parameter_product (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
    (f g : R) (hfg : Ideal.span {f, g} = maximalIdeal R) :
    IsStrictNormalCrossingsEquation R (f * g) := by
  refine Or.inr ⟨2, ![f, g], ⟨hR, ?_, ?_⟩, 2, Nat.zero_lt_succ 1, le_rfl, 1, ?_⟩
  · simpa using hdim
  · simpa only [Matrix.range_cons_cons_empty] using hfg
  · simp [Fin.prod_univ_two]

end IsStrictNormalCrossingsEquation

/-- Strict normal crossings of an effective Cartier divisor, expressed in
every original regular equation chart on an integral locally Noetherian scheme.
The regular equation cover supplies effectivity, independently of SNC. -/
def IsStrictNormalCrossingsCartier (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] (D : CartierDivisor X) : Prop :=
  HasRegularCartierEquations X D ∧
    ∀ (c : RegularCartierEquationChart X D) (x : X) (hx : x ∈ c.chart.openSet),
      IsStrictNormalCrossingsEquation (X.presheaf.stalk x)
        (X.presheaf.germ c.chart.openSet x hx c.coefficient)

end KltDP.Geometry
