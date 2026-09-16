/-
Original project definition and proof adapters. Released under Apache 2.0;
see docs/reuse_sources/literal_coherent_module/sources/mathlib/LICENSE.txt.
The mathematical definition follows the literal Stacks Project Tag 01BV;
its separately licensed frozen source and correspondence are recorded in
docs/reuse_sources/literal_coherent_module/CORRESPONDENCE.md.
-/
import KltDP.Geometry.NoetherianUnitKernel

/-!
# Literal coherence of original scheme-module sheaves

Coherence means finite type and finite-type kernels for every finite
family of original sections on every open. The associated map uses the
original free sheaf, the original Over restriction and the proved
free-map/section equivalence. Neither surjectivity of the family nor
finite presentation is part of the definition.

The structure sheaf of an actual locally Noetherian scheme is coherent
by the previously constructed all-open kernel theorem. This does not
assert the general equivalence between coherence and finite presentation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (M : X.Modules)

/-- Original finite-free maps correspond to families of original sections
on the open, using their actual compatible restrictions on its Over site.
The equivalence itself does not require the index type to be finite. -/
def freeHomSectionsEquiv (U : X.Opens) (I : Type u) :
    (_root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶ M.over U) ≃
      (I → M.val.obj (op U)) :=
  (M.over U).freeHomEquiv.trans
    (Equiv.piCongrRight (fun _ : I =>
      _root_.SheafOfModules.overSectionsEquiv X.ringCatSheaf M U))

/-- The actual morphism associated to the given family of sections. -/
def sectionFamilyHom (U : X.Opens) {I : Type u}
    (s : I → M.val.obj (op U)) :
    _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶ M.over U :=
  (freeHomSectionsEquiv M U I).symm s

/-- The generator section on each smaller open is the original
restriction of the specified section, as required by the associated map. -/
theorem sectionFamilyHom_generator_restrict (U : X.Opens) {I : Type u}
    (s : I → M.val.obj (op U)) (i : I) (V : (Over U)ᵒᵖ) :
    (((M.over U).freeHomEquiv (sectionFamilyHom M U s)) i).val V =
      M.val.map V.unop.hom.op (s i) := by
  change (((M.over U).freeHomEquiv
      ((M.over U).freeHomEquiv.symm (fun j =>
        (_root_.SheafOfModules.overSectionsEquiv X.ringCatSheaf M U).symm
          (s j)))) i).val V = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Stacks 01BV on the actual scheme-module sheaf: finite type and the
finite-kernel condition for every open and every finite section family.
Empty families are included; no epimorphism condition is imposed. -/
class IsCoherentModule : Prop where
  finiteType : _root_.SheafOfModules.IsFiniteType M
  finiteKernel (U : X.Opens) (I : Type u) [Finite I]
    (s : I → M.val.obj (op U)) :
    _root_.SheafOfModules.IsFiniteType (kernel (sectionFamilyHom M U s))

instance IsCoherentModule.isFiniteType [h : IsCoherentModule M] :
    _root_.SheafOfModules.IsFiniteType M := h.finiteType

/-- The literal section-family condition applies to every original
finite-free map, by the proved equivalence, without an epi premise. -/
theorem IsCoherentModule.kernel_finiteType [h : IsCoherentModule M]
    (U : X.Opens) (I : Type u) [Finite I]
    (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶ M.over U) :
    _root_.SheafOfModules.IsFiniteType (kernel φ) := by
  have hφ := h.finiteKernel U I (freeHomSectionsEquiv M U I φ)
  simpa only [sectionFamilyHom, Equiv.symm_apply_apply] using hφ

/-- Conversely, finite type and the actual all-open finite-free-map
kernel condition prove the literal section-family definition. -/
theorem IsCoherentModule.of_kernel_finiteType
    [_root_.SheafOfModules.IsFiniteType M]
    (h : ∀ (U : X.Opens) (I : Type u) [Finite I]
      (φ : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶ M.over U),
      _root_.SheafOfModules.IsFiniteType (kernel φ)) : IsCoherentModule M := by
  refine ⟨inferInstance, ?_⟩
  intro U I hI s
  exact h U I (sectionFamilyHom M U s)

/-- The original structure sheaf is coherent on every actual locally
Noetherian scheme. Only actual affine section rings entered the kernel
proof; no Noetherianity of sections on arbitrary opens is assumed. -/
instance unit_isCoherentModule (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsCoherentModule (_root_.SheafOfModules.unit X.ringCatSheaf) :=
  IsCoherentModule.of_kernel_finiteType _
    (fun U I _ φ => isFiniteType_kernel_free_to_restricted_unit U I φ)

end KltDP.Geometry
