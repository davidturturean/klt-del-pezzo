import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Group.Equiv.Basic

/-! The pinned additive-hom equivalence transports the actual integral dual
along an additive isometry. No finiteness or freeness is needed. -/

set_option autoImplicit false
noncomputable section

namespace KltDP.LinearAlgebra

/-- Bijectivity of the actual map to the additive integral dual is invariant
under the supplied additive isometry of the two bilinear forms. -/
theorem dual_bijective_iff_of_isometry
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (F : LinearMap.BilinForm ℤ A) (G : LinearMap.BilinForm ℤ B)
    (e : A ≃+ B) (he : ∀ a b, G (e a) (e b) = F a b) :
    Function.Bijective (fun b => (G b).toAddMonoidHom) ↔
      Function.Bijective (fun a => (F a).toAddMonoidHom) := by
  let d : (A →+ ℤ) ≃+ (B →+ ℤ) := AddEquiv.addMonoidHomCongr e (AddEquiv.refl ℤ)
  have h : (fun b => (G b).toAddMonoidHom) =
      ((fun l : A →+ ℤ => d l) ∘ (fun a => (F a).toAddMonoidHom)) ∘ e.symm := by
    funext b
    apply AddMonoidHom.ext
    intro z
    obtain ⟨b, rfl⟩ := e.surjective b
    obtain ⟨z, rfl⟩ := e.surjective z
    change G (e b) (e z) = F (e.symm (e b)) (e.symm (e z))
    rw [he, e.symm_apply_apply, e.symm_apply_apply]
  rw [h, Function.Bijective.of_comp_iff _ e.symm.bijective,
    Function.Bijective.of_comp_iff' d.bijective]

end KltDP.LinearAlgebra

#check @KltDP.LinearAlgebra.dual_bijective_iff_of_isometry
#print axioms KltDP.LinearAlgebra.dual_bijective_iff_of_isometry
