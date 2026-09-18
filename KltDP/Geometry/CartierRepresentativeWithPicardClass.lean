import KltDP.Geometry.QCartierFromWeilClass
import KltDP.Geometry.PicardWeilClassHom

/-!
The actual principal correction producing a Cartier representative also
preserves its original Picard class. This retains the line sheaf needed
to establish ampleness of an actual Cartier multiple.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Correcting by the original rational function preserves the original
Cartier Picard class as well as giving the specified Weil divisor. -/
theorem exists_cartier_representative_with_picardClass
    (D : X.WeilDivisor) (A : CartierDivisor X.toScheme)
    (h : X.weilClassMap D = X.weilClassMap (X.cartierToWeilHom A)) :
    ∃ B : CartierDivisor X.toScheme,
      X.cartierToWeilHom B = D ∧
      cartierPicardHom X.toScheme B = cartierPicardHom X.toScheme A := by
  obtain ⟨f, hf⟩ := (X.weilClassMap_eq_iff D (X.cartierToWeilHom A)).mp h
  refine ⟨principalCartierDivisorHom X.toScheme (Additive.ofMul f) + A, ?_, ?_⟩
  · rw [map_add, X.cartierToWeilHom_principal, ← hf]
    exact sub_add_cancel D (X.cartierToWeilHom A)
  · rw [map_add, cartierPicardHom_principal, zero_add]

/-- A specified original sheaf Picard class has an actual Cartier
representative whenever its Weil class is the specified divisor class. -/
theorem exists_cartier_representative_of_picardWeilClass_eq
    (D : X.WeilDivisor) (L : Additive X.toScheme.Pic)
    (h : X.weilClassMap D = X.picardToWeilClassHom L) :
    ∃ B : CartierDivisor X.toScheme,
      X.cartierToWeilHom B = D ∧ cartierPicardHom X.toScheme B = L := by
  obtain ⟨A, hA⟩ := cartierPicardHom_surjective X.toScheme L
  have hclass : X.weilClassMap D = X.weilClassMap (X.cartierToWeilHom A) :=
    h.trans ((congrArg X.picardToWeilClassHom hA).symm.trans
      (X.picardToWeilClassHom_cartierPicardHom A))
  obtain ⟨B, hB, hPic⟩ := X.exists_cartier_representative_with_picardClass D A hclass
  exact ⟨B, hB, hPic.trans hA⟩

end KltDP.Geometry.NormalProjectiveSurface
