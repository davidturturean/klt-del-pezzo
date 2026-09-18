import KltDP.Geometry.CartierPicardEndpointRational
import KltDP.Geometry.CartierWeilClassMap

/-!
# Actual Cartier multiples obtained from an integral Weil class relation

A principal correction turns equality with a Cartier class into an actual
Cartier representative. Applying this to a positive multiple gives the existing
Q-Cartier predicate, with a witness in the original Cartier divisor group.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Equality with a Cartier class produces an actual Cartier representative;
the correcting function is supplied by the original Weil quotient relation. -/
theorem exists_cartier_representative_of_weilClass_eq
    (D : X.WeilDivisor) (A : CartierDivisor X.toScheme)
    (h : X.weilClassMap D = X.weilClassMap (X.cartierToWeilHom A)) :
    ∃ B : CartierDivisor X.toScheme, X.cartierToWeilHom B = D := by
  obtain ⟨f, hf⟩ := (X.weilClassMap_eq_iff D (X.cartierToWeilHom A)).mp h
  refine ⟨principalCartierDivisorHom X.toScheme (Additive.ofMul f) + A, ?_⟩
  rw [map_add, X.cartierToWeilHom_principal, ← hf]
  exact sub_add_cancel D (X.cartierToWeilHom A)

/-- A positive multiple equal to an actual Cartier class is Q-Cartier in
the original rational divisor space, with no index fixed in advance. -/
theorem qCartier_of_positive_multiple_weilClass_eq
    (D : X.WeilDivisor) (m : ℕ) (hm : 0 < m)
    (A : CartierDivisor X.toScheme)
    (h : m • X.weilClassMap D = X.weilClassMap (X.cartierToWeilHom A)) :
    X.QCartier (rationalizeWeilDivisor X D) := by
  apply (X.qCartier_integral_iff D).mpr
  refine ⟨m, hm, ?_⟩
  apply X.exists_cartier_representative_of_weilClass_eq (m • D) A
  simpa only [map_nsmul] using h

/-- The signed integral relation arising in canonical descent gives an
actual positive Cartier multiple of the original Weil divisor. -/
theorem qCartier_of_positive_weilClass_relation
    (D : X.WeilDivisor) (m : ℕ) (hm : 0 < m)
    (A : CartierDivisor X.toScheme) (d : ℤ)
    (h : m • X.weilClassMap D + d • X.weilClassMap (X.cartierToWeilHom A) = 0) :
    X.QCartier (rationalizeWeilDivisor X D) := by
  apply X.qCartier_of_positive_multiple_weilClass_eq D m hm (-(d • A))
  simpa only [map_neg, map_zsmul] using eq_neg_of_add_eq_zero_left h

/-- The same criterion accepts the positive signed coefficient of an
integral canonical identity, converting it to a natural multiple internally. -/
theorem qCartier_of_positive_int_weilClass_relation
    (D : X.WeilDivisor) (m : ℤ) (hm : 0 < m)
    (A : CartierDivisor X.toScheme) (d : ℤ)
    (h : m • X.weilClassMap D + d • X.weilClassMap (X.cartierToWeilHom A) = 0) :
    X.QCartier (rationalizeWeilDivisor X D) := by
  have hmcast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm)
  have hmpos : 0 < m.toNat := Nat.pos_of_ne_zero (by
    intro hz
    exact (ne_of_gt hm) (hmcast.symm.trans (congrArg (fun t : ℕ => (t : ℤ)) hz)))
  apply X.qCartier_of_positive_weilClass_relation D m.toNat hmpos A d
  simpa only [← natCast_zsmul, hmcast] using h

end KltDP.Geometry.NormalProjectiveSurface
