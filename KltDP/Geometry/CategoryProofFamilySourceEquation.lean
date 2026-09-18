import Mathlib.CategoryTheory.Category.Basic

/-! Change one proof parameter of an arbitrary source map in an arbitrary category. -/

open CategoryTheory
universe u v
namespace KltDP.Geometry.CategoryProofFamilySourceEquation

/-- Proof irrelevance acts on the parameter before applying the source-map family. -/
theorem replace_proof {C : Type u} [Category.{v} C] {M N T : C}
    {P : Prop} (F : P → (M ⟶ N)) (old : P)
    {l : M ⟶ T} {a : N ⟶ T}
    (h : l = F old ≫ a) (new : P) : l = F new ≫ a :=
  h.trans (congrArg (fun p => F p ≫ a) (Subsingleton.elim old new))

end KltDP.Geometry.CategoryProofFamilySourceEquation
