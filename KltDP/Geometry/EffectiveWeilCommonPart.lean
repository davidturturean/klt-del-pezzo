import KltDP.Geometry.RegularSurfaceWeilPicard
import Mathlib.Data.Finsupp.Order

/-! The actual coefficientwise common divisor of two original Weil members.
Subtracting this common divisor gives effective residuals with no common
prime component and preserves the same rational-function linear equivalence. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The common divisor of two effective original members is effective. -/
theorem commonWeilPart_effective (D E : X.WeilDivisor)
    (hD : EffectiveDivisor D) (hE : EffectiveDivisor E) : EffectiveDivisor (D ⊓ E) := by
  intro C
  simpa only [Finsupp.inf_apply] using (le_inf (hD C) (hE C))

/-- Subtracting the common part leaves an effective original left member. -/
theorem commonWeilPart_left_effective (D E : X.WeilDivisor) :
    EffectiveDivisor (D - (D ⊓ E)) := by
  intro C
  simpa only [Finsupp.sub_apply, Finsupp.inf_apply] using
    (sub_nonneg.mpr (inf_le_left : D C ⊓ E C ≤ D C))

/-- Subtracting the same common part leaves an effective original right member. -/
theorem commonWeilPart_right_effective (D E : X.WeilDivisor) :
    EffectiveDivisor (E - (D ⊓ E)) := by
  intro C
  simpa only [Finsupp.sub_apply, Finsupp.inf_apply] using
    (sub_nonneg.mpr (inf_le_right : D C ⊓ E C ≤ E C))

/-- The two original residual divisors have no common prime component. -/
theorem commonWeilPart_residual_supports_disjoint (D E : X.WeilDivisor) :
    Disjoint (D - (D ⊓ E)).support (E - (D ⊓ E)).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hC hC'
  have hd := Finsupp.mem_support_iff.mp hC
  have he := Finsupp.mem_support_iff.mp hC'
  simp only [Finsupp.sub_apply, Finsupp.inf_apply] at hd he
  rcases le_total (D C) (E C) with h | h
  · exact hd (by rw [inf_eq_left.mpr h, sub_self])
  · exact he (by rw [inf_eq_right.mpr h, sub_self])

/-- Subtraction of a common actual divisor preserves the original principal witness. -/
theorem linearlyEquivalent_sub_common {D E : X.WeilDivisor}
    (h : X.LinearlyEquivalent D E) (Z : X.WeilDivisor) :
    X.LinearlyEquivalent (D - Z) (E - Z) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_⟩
  calc
    (D - Z) - (E - Z) = D - E := by abel
    _ = X.principalDivisor q := hq

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.commonWeilPart_residual_supports_disjoint
#print axioms KltDP.Geometry.NormalProjectiveSurface.linearlyEquivalent_sub_common
