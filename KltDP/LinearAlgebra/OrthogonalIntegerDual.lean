import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Ring

/-!
# An orthogonal summand of square minus one preserves the integral dual test

This is the additive-group form needed by the original PicardUnimodular
predicate. The pinned dual-product equivalence treats linear duals; here
restriction and extension of actual additive functionals give both directions
directly, without finite rank, freeness or nondegeneracy assumptions.
-/

set_option autoImplicit false
noncomputable section

namespace KltDP.LinearAlgebra

/-- Orthogonally adjoining the integral form [-1] preserves bijectivity
of the actual map to the additive integral dual. -/
theorem dual_bijective_iff_of_orthogonal_int
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (F : LinearMap.BilinForm ℤ A) (G : LinearMap.BilinForm ℤ B)
    (e : (A × ℤ) ≃+ B)
    (he : ∀ x y, G (e x) (e y) = F x.1 y.1 - x.2 * y.2) :
    Function.Bijective (fun b => (G b).toAddMonoidHom) ↔
      Function.Bijective (fun a => (F a).toAddMonoidHom) := by
  constructor
  · intro hG
    constructor
    · intro a b hab
      have h : (G (e (a, 0))).toAddMonoidHom = (G (e (b, 0))).toAddMonoidHom := by
        apply AddMonoidHom.ext
        intro z
        obtain ⟨z, rfl⟩ := e.surjective z
        change G (e (a, 0)) (e z) = G (e (b, 0)) (e z)
        rw [he, he]
        exact congrArg (fun l : A →+ ℤ => l z.1 - 0 * z.2) hab
      exact congrArg Prod.fst (e.injective (hG.injective h))
    · intro f
      let l : B →+ ℤ := f.comp ((AddMonoidHom.fst A ℤ).comp e.symm.toAddMonoidHom)
      obtain ⟨b, hb⟩ := hG.surjective l
      obtain ⟨b, rfl⟩ := e.surjective b
      refine ⟨b.1, ?_⟩
      apply AddMonoidHom.ext
      intro a
      have h := congrArg (fun l : B →+ ℤ => l (e (a, 0))) hb
      change G (e b) (e (a, 0)) = f (e.symm (e (a, 0))).1 at h
      simpa only [he, mul_zero, sub_zero, AddEquiv.symm_apply_apply] using h
  · intro hF
    constructor
    · intro a b hab
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      have hn : a.2 = b.2 := by
        have h := congrArg (fun l : B →+ ℤ => l (e (0, 1))) hab
        change G (e a) (e (0, 1)) = G (e b) (e (0, 1)) at h
        simpa only [he, map_zero, mul_one, zero_sub, neg_inj] using h
      have ha : a.1 = b.1 := by
        apply hF.injective
        apply AddMonoidHom.ext
        intro c
        have h := congrArg (fun l : B →+ ℤ => l (e (c, 0))) hab
        change G (e a) (e (c, 0)) = G (e b) (e (c, 0)) at h
        simpa only [he, mul_zero, sub_zero] using h
      exact congrArg e (Prod.ext ha hn)
    · intro f
      let l : A →+ ℤ := (f.comp e.toAddMonoidHom).comp (AddMonoidHom.inl A ℤ)
      obtain ⟨a, ha⟩ := hF.surjective l
      refine ⟨e (a, -f (e (0, 1))), ?_⟩
      apply AddMonoidHom.ext
      intro b
      obtain ⟨⟨b, n⟩, rfl⟩ := e.surjective b
      have hfa : F a b = f (e (b, 0)) :=
        congrArg (fun l : A →+ ℤ => l b) ha
      have hsplit : (b, n) = (b, 0) + n • (0, 1) := by
        apply Prod.ext
        · simp
        · change n = 0 + n • (1 : ℤ)
          simp only [smul_eq_mul, mul_one, zero_add]
      have hf : f (e (b, n)) = f (e (b, 0)) + n * f (e (0, 1)) := by
        exact (congrArg (fun z => f (e z)) hsplit).trans
          (by simp only [map_add, map_zsmul, smul_eq_mul])
      change G (e (a, -f (e (0, 1)))) (e (b, n)) = f (e (b, n))
      rw [he, hfa, hf]
      ring

end KltDP.LinearAlgebra

#check @KltDP.LinearAlgebra.dual_bijective_iff_of_orthogonal_int
#print axioms KltDP.LinearAlgebra.dual_bijective_iff_of_orthogonal_int
