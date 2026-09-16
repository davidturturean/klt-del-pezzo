import KltDP.Compatibility.SheafIsoOnBasis
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Detecting actual module-sheaf epimorphisms on an open basis

Surjectivity of the original section maps on a topological basis gives
local surjectivity of the underlying additive sheaf. The pinned local
surjectivity theorem and the faithful forgetful functor then give an
epimorphism of the original module sheaves. Surjectivity on arbitrary
opens is not needed.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.SheafOfModules

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : TopCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} R} {ι : Type*} {B : ι → Opens X}

/-- Surjective section maps on an actual open basis give an epimorphism
of the original module sheaves. -/
theorem epi_of_surjective_on_basis (φ : M ⟶ N)
    (h : Opens.IsBasis (Set.range B))
    (hi : ∀ i, Function.Surjective (φ.val.app (op (B i)))) : Epi φ := by
  haveI : Sheaf.IsLocallySurjective ((_root_.SheafOfModules.toSheaf R).map φ) := by
    constructor
    intro U s
    change ∀ x ∈ U, ∃ (V : Opens X) (j : V ⟶ U),
      (Presheaf.imageSieve ((_root_.SheafOfModules.toSheaf R).map φ).val s) j ∧ x ∈ V
    intro x hx
    obtain ⟨V, ⟨i, rfl⟩, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp h hx
    refine ⟨B i, homOfLE hVU, ?_, hxV⟩
    exact hi i (N.val.map (homOfLE hVU).op s)
  exact (_root_.SheafOfModules.toSheaf R).epi_of_epi_map inferInstance

end KltDP.SheafOfModules
