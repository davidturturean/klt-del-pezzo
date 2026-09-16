import KltDP.Compatibility.SheafLocalQuotient
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Sections in the kernel of a quotient by a subsheaf

For a monomorphism of actual sheaves of abelian groups, a section maps to
zero in the cokernel exactly when it comes from the source sheaf on the
same open set.

The proof reuses pinned Mathlib's `Abelian.monoIsKernelOfCokernel` and
`KernelFork.mapIsLimit`. The sheaf-to-presheaf functor and evaluation
preserve the actual kernel. `ShortComplex.ab_exact_iff_function_exact`
then gives the statement about sections. No exactness of sectionwise
cokernels or surjectivity on sections is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Sheaf

variable {X : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrp.{u} X}
  (φ : F ⟶ G) [Mono φ]

/-- For an actual subsheaf, the kernel of its quotient is computed on sections. -/
theorem toQuotientSheaf_app_eq_zero_iff_of_mono (U : Opens X) (s : G.val.obj (op U)) :
    (toQuotientSheaf φ).val.app (op U) s = 0 ↔
      ∃ r : F.val.obj (op U), φ.val.app (op U) r = s := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrp.{u} X) :=
    ShortComplex.mk φ (toQuotientSheaf φ) (toQuotientSheaf_condition φ)
  let ev : TopCat.Sheaf AddCommGrp.{u} X ⥤ AddCommGrp.{u} :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrp.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrp.{u}).obj (op U)
  letI : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  letI : PreservesLimitsOfShape WalkingParallelPair
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) := by
    infer_instance
  letI : PreservesLimitsOfShape WalkingParallelPair
      ((evaluation (Opens X)ᵒᵖ AddCommGrp.{u}).obj (op U)) := by
    infer_instance
  letI : PreservesLimitsOfShape WalkingParallelPair ev := by
    dsimp only [ev]
    infer_instance
  have hK : IsLimit (KernelFork.ofι S.f S.zero) :=
    Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ)) (cokernelIsCokernel φ)
  have hExact : (S.map ev).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hK ev)
  exact ((S.map ev).ab_exact_iff_function_exact.mp hExact) s

end KltDP.Sheaf
