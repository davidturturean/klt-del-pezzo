import KltDP.Geometry.AmpleSerreDegreeBound
import KltDP.Geometry.AmpleNefCartierSum
import KltDP.Geometry.ProjectiveAmpleCartierWitness
import KltDP.Geometry.RegularSurfaceSmoothLiteralUse
import Mathlib.Tactic.Abel

/-!
# Every original Cartier divisor is a difference of ample Cartier divisors

Serre's actual global-generation bound makes NH+D nef, uniformly on every
original prime curve. The proved ample-plus-nef theorem makes H+NH+D ample,
while the original positive power (N+1)H is ample. Their literal Cartier
difference is D. The smoothness needed by the existing ample-plus-nef proof
is derived from the original surface regularity over the algebraically closed field.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CanonicalAmpleSpan

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

theorem exists_nef_twist (H D : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H)) :
    ∃ N : ℕ, Positivity.IsNef S.structureMorphism
      (cartierDivisorInvertibleSheaf S.toScheme (N • H + D)) := by
  obtain ⟨N, hN⟩ := AmpleSerreDegreeBound.eventually_twisted_restrictionDegree_nonneg S
    (cartierDivisorInvertibleSheaf S.toScheme H) hH (cartierDivisorInvertibleSheaf S.toScheme D)
  refine ⟨N, (Positivity.isNef_iff_forall_primeCurve S _).mpr ?_⟩
  intro C
  rw [← C.intersectionNumber_eq_restrictionDegree, ← C.intersectionNumberHom_apply,
    map_add, map_nsmul, C.intersectionNumberHom_apply, C.intersectionNumberHom_apply]
  simpa only [nsmul_eq_mul] using hN N le_rfl C

/-- Both ample divisors are actual Cartier divisors and the equality holds
in the original Cartier group, before any numerical quotient. -/
theorem exists_difference_of_ample
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x) (D : CartierDivisor S.toScheme) :
    ∃ A B : CartierDivisor S.toScheme,
      AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme A) ∧
      AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme B) ∧ D = A - B := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hregular
  obtain ⟨H, hH⟩ := S.exists_isAmple_cartier
  obtain ⟨N, hN⟩ := exists_nef_twist S H D hH
  have hA := AmpleNefCartierSum.isAmple_add S H (N • H + D) hH hN
  have hB : AmpleSerre.IsAmple
      (cartierDivisorInvertibleSheaf S.toScheme ((N + 1) • H)) := by
    apply AmplePositivity.isAmple_pow (L := cartierDivisorInvertibleSheaf S.toScheme H)
      (N + 1) (Nat.succ_pos N) ?_ hH
    change (cartierPicardHom S.toScheme ((N + 1) • H)).toMul =
      (cartierPicardHom S.toScheme H).toMul ^ (N + 1)
    rw [map_nsmul, toMul_nsmul]
  refine ⟨H + (N • H + D), (N + 1) • H, hA, hB, ?_⟩
  rw [add_nsmul, one_nsmul]
  abel

end KltDP.Geometry.CanonicalAmpleSpan

#check @KltDP.Geometry.CanonicalAmpleSpan.exists_nef_twist
#check @KltDP.Geometry.CanonicalAmpleSpan.exists_difference_of_ample
#print axioms KltDP.Geometry.CanonicalAmpleSpan.exists_difference_of_ample
