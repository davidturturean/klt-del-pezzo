import KltDP.Compatibility.SheafSubmodule
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Generating sections detect proper submodules of actual module sheaves

If every member of a generating family lies in an actual subsheaf of modules,
the free presentation factors through its inclusion.  That inclusion is then
both mono and epi in the abelian category of module sheaves, hence is an
isomorphism.  Consequently every original section lies in the subsheaf.

This reuses the pinned coproduct presentation and the accepted, reviewed
newer-Mathlib submodule port.  It supplies a categorical step for detecting a
generator outside the maximal-ideal subsheaf at a point.
-/

noncomputable section

open CategoryTheory Opposite

universe u v w

namespace KltDP.SheafGeneratorSubmodule

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  {M : _root_.SheafOfModules.{u} R}

/-- A genuine generating family cannot be contained in a proper module
subsheaf.  Membership of arbitrary original sections is derived from the
epimorphic free presentation. -/
theorem section_mem_of_generators_mem (G : M.GeneratingSections) (P : M.Submodule)
    (hG : ∀ (i : G.I) (V : Cᵒᵖ), (G.s i).val V ∈ P.obj V)
    (V : Cᵒᵖ) (m : M.val.obj V) : m ∈ P.obj V := by
  let s : G.I → P.toSheafOfModules.sections := fun i => {
    val W := ⟨(G.s i).val W, hG i W⟩
    property g := Subtype.ext ((G.s i).property g) }
  let a : _root_.SheafOfModules.free G.I ⟶ P.toSheafOfModules :=
    P.toSheafOfModules.freeHomEquiv.symm s
  have ha : a ≫ P.ι = G.π := by
    change P.toSheafOfModules.freeHomEquiv.symm s ≫ P.ι = M.freeHomEquiv.symm G.s
    rw [_root_.SheafOfModules.freeHomEquiv_symm_comp]
    rfl
  letI : Epi P.ι := epi_of_epi_fac ha
  letI : IsIso P.ι := isIso_of_mono_of_epi P.ι
  let t : P.obj V := (inv P.ι).val.app V m
  have ht : t.val = m :=
    congrArg (fun f : M ⟶ M => f.val.app V m) (IsIso.inv_hom_id P.ι)
  exact ht ▸ t.property

end KltDP.SheafGeneratorSubmodule
