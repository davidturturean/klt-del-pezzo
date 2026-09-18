import KltDP.Geometry.ContractionPicardUnimodular

/-! Injectivity into the actual integral dual makes the original additive
Picard group torsion-free. This uses only the existing original pairing. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

/-- The original integral-dual unimodularity predicate implies the original
Picard torsion-freeness predicate, without choosing generators or a basis. -/
theorem picardTorsionFree_of_picardUnimodular
    {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (h : S.PicardUnimodular hS) : S.PicardTorsionFree := by
  have hinj := ((S.picardUnimodular_iff_bilinForm hS).mp h).injective
  intro p n hn hp
  apply hinj
  apply AddMonoidHom.ext
  intro q
  let B := S.integralPicardIntersectionBilinForm hS
  change B p q = B 0 q
  have hz : n • B p q = 0 := by
    have he := congrArg (fun a => B a q) hp
    simpa only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply] using he
  rw [nsmul_eq_mul] at hz
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hpq : B p q = 0 := (mul_eq_zero.mp hz).resolve_left hnz
  simpa only [map_zero, LinearMap.zero_apply] using hpq

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.picardTorsionFree_of_picardUnimodular
#print axioms KltDP.Geometry.NormalProjectiveSurface.picardTorsionFree_of_picardUnimodular
