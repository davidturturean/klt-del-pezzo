import Mathlib.CategoryTheory.Iso

/-! A generic common-target isomorphism and its cancellation identity. -/

open CategoryTheory

universe v u

namespace KltDP.Geometry.CanonicalExteriorIsoCancellation

variable {C : Type u} [Category.{v} C] {M N P : C}

/-- Compare two objects through their given common target. -/
def comparison (e : M ≅ P) (e' : N ≅ P) : M ≅ N := e ≪≫ e'.symm

/-- Prove cancellation while the objects and both isomorphisms remain abstract. -/
theorem comparison_hom_comp (e : M ≅ P) (e' : N ≅ P) :
    (comparison e e').hom ≫ e'.hom = e.hom := by
  simp only [comparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end KltDP.Geometry.CanonicalExteriorIsoCancellation
