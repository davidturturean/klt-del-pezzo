import KltDP.Geometry.CartierRepresentativeWithPicardClass
import KltDP.Geometry.AmplePositivity

/-!
A positive ample Picard class representing an original Weil divisor
produces an actual ample Cartier divisor with that exact Weil divisor.
Applied to a canonical relation, this gives an ample Cartier multiple
of the actual anticanonical divisor.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Equality with a positive power of an ample original line produces
an ample Cartier representative of the actual Weil divisor. -/
theorem exists_ample_cartier_representative_of_picardWeilClass_eq
    (D : X.WeilDivisor) (L : InvertibleSheaf X.toScheme)
    (d : ℕ) (hd : 0 < d) (hL : AmpleSerre.IsAmple L)
    (h : X.weilClassMap D =
      X.picardToWeilClassHom (d • Additive.ofMul L.toPic)) :
    ∃ B : CartierDivisor X.toScheme,
      X.cartierToWeilHom B = D ∧
      AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme B) := by
  obtain ⟨B, hB, hPic⟩ := X.exists_cartier_representative_of_picardWeilClass_eq
    D (d • Additive.ofMul L.toPic) h
  refine ⟨B, hB, AmplePositivity.isAmple_pow d hd ?_ hL⟩
  change cartierPicardClass X.toScheme B = L.toPic ^ d
  exact congrArg Additive.toMul (hPic.trans (_root_.ofMul_pow d L.toPic).symm)

/-- A signed positive canonical-class relation gives an exact ample
Cartier multiple of the original negative Weil divisor. -/
theorem exists_ample_anticanonical_multiple_of_positive_relation
    (D : X.WeilDivisor) (L : InvertibleSheaf X.toScheme)
    (m d : ℤ) (hm : 0 < m) (hd : 0 < d) (hL : AmpleSerre.IsAmple L)
    (h : m • X.weilClassMap D +
      d • X.picardToWeilClassHom (Additive.ofMul L.toPic) = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : CartierDivisor X.toScheme,
      X.cartierToWeilHom B = N • (-D) ∧
      AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme B) := by
  have hmcast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm)
  have hdcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hd)
  have hmpos : 0 < m.toNat := Nat.pos_of_ne_zero (by
    intro hz
    exact (ne_of_gt hm) (hmcast.symm.trans (congrArg (fun t : ℕ => (t : ℤ)) hz)))
  have hdpos : 0 < d.toNat := Nat.pos_of_ne_zero (by
    intro hz
    exact (ne_of_gt hd) (hdcast.symm.trans (congrArg (fun t : ℕ => (t : ℤ)) hz)))
  refine ⟨m.toNat, hmpos, ?_⟩
  apply X.exists_ample_cartier_representative_of_picardWeilClass_eq
    (m.toNat • (-D)) L d.toNat hdpos hL
  have hneg : -(m • X.weilClassMap D) =
      d • X.picardToWeilClassHom (Additive.ofMul L.toPic) :=
    by
      have hh := congrArg (fun z : X.WeilClassGroup => -z)
        (eq_neg_of_add_eq_zero_left h)
      simpa only [neg_neg] using hh
  simpa only [map_nsmul, map_zsmul, map_neg, nsmul_neg, zsmul_neg, ← natCast_zsmul,
    hmcast, hdcast] using hneg

end KltDP.Geometry.NormalProjectiveSurface
