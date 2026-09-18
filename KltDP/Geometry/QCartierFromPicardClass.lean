import KltDP.Geometry.QCartierFromWeilClass
import KltDP.Geometry.PicardWeilClassHom

/-!
# A positive Weil class relation with an original Picard class

The integral Cartier representative of the actual target Picard class is
constructed by the existing equivalence. The positive-multiple criterion
then supplies Q-Cartierness in the original rational Weil divisor space.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- An integral relation with an actual target line class gives a Cartier
multiple; no Cartier representative or divisor-class comparison is assumed. -/
theorem qCartier_of_positive_int_picard_relation
    (D : X.WeilDivisor) (m : ℤ) (hm : 0 < m)
    (L : X.toScheme.Pic) (d : ℤ)
    (h : m • X.weilClassMap D + d • X.picardToWeilClassHom (Additive.ofMul L) = 0) :
    X.QCartier (rationalizeWeilDivisor X D) := by
  obtain ⟨A, rfl⟩ := cartierPicardClass_surjective X.toScheme L
  apply X.qCartier_of_positive_int_weilClass_relation D m hm A d
  change m • X.weilClassMap D +
    d • X.picardToWeilClassHom (cartierPicardHom X.toScheme A) = 0 at h
  simpa only [X.picardToWeilClassHom_cartierPicardHom] using h

end KltDP.Geometry.NormalProjectiveSurface
