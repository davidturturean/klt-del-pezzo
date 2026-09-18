import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Ring.Parity

/-!
# Even pairings on an orthogonal submodule plus the original generated span

The supplied vectors pair to zero with the original submodule and evenly
with one another. Span induction and the actual supremum decomposition
therefore give even pairings with every element of the supplied submodule.
The index type need not be finite, and the form need not be symmetric.
-/

set_option autoImplicit false

namespace KltDP.Lattices.OrthogonalSpanEven

variable {M ι : Type*} [AddCommGroup M] [Module ℤ M]

/-- Even generator pairings extend across the original span and its
sum with the original orthogonal submodule. -/
theorem even_pairing
    (B : LinearMap.BilinForm ℤ M) (v : ι → M)
    (Γ Γ0 : Submodule ℤ M)
    (hΓ : Γ = Γ0 ⊔ Submodule.span ℤ (Set.range v))
    (horth : ∀ i, ∀ y ∈ Γ0, B (v i) y = 0)
    (hgen : ∀ i j, Even (B (v i) (v j))) :
    ∀ i, ∀ y ∈ Γ, Even (B (v i) y) := by
  intro i y hy
  rw [hΓ] at hy
  obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, horth i x hx, zero_add]
  refine Submodule.span_induction
    (p := fun w _ => Even (B (v i) w)) ?_ ?_ ?_ ?_ hz
  · rintro w ⟨j, rfl⟩
    exact hgen i j
  · simpa only [map_zero] using (Even.zero : Even (0 : ℤ))
  · intro a b _ _ ha hb
    simpa only [map_add] using ha.add hb
  · intro a w _ hw
    simpa only [map_smul, smul_eq_mul] using hw.mul_left a

end KltDP.Lattices.OrthogonalSpanEven

#check @KltDP.Lattices.OrthogonalSpanEven.even_pairing
#print axioms KltDP.Lattices.OrthogonalSpanEven.even_pairing
