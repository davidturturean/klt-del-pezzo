import KltDP.Geometry.InvertibleTensorExact
import KltDP.Geometry.SchemeStructureTensor

/-!
# An actual nonzero section gives the original twisted line-bundle map

Tensor the original structure-module map of a section with an original
invertible sheaf. The existing tensor equivalence is faithful and preserves
zero maps, so a nonzero original top value gives a nonzero actual sheaf map.
An actual target isomorphism transports that map to any specified original
line-bundle representative. No numerical or section-existence input is added.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.InvertibleSectionTwistMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance tensorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance symmetricModules (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

variable {X : Scheme.{u}}

private def leftStructureIso (H : InvertibleSheaf X) :
    _root_.SheafOfModules.unit X.ringCatSheaf ⊗ H.obj ≅ H.obj :=
  BraidedCategory.braiding _ H.obj ≪≫ schemeStructureTensorRightIso H.obj

private theorem tensorRight_faithful (H : InvertibleSheaf X) :
    (tensorRight H.obj).Faithful := by
  obtain ⟨H', ⟨e⟩, ⟨e'⟩⟩ := H.exists_tensorInverse
  exact inferInstanceAs (KltDP.Monoidal.tensorRightEquivalence H.obj H' e e').functor.Faithful

/-- A nonzero original top value makes the original structure-module map nonzero. -/
theorem sectionHom_ne_zero (N : X.Modules) (s : N.sections)
    (hs : s.val (op ⊤) ≠ 0) : N.unitHomEquiv.symm s ≠ 0 := by
  intro hz
  have heval : (N.unitHomEquiv.symm s).val.app (op ⊤) (1 : Γ(X, ⊤)) =
      s.val (op ⊤) :=
    congrArg (fun t : N.sections => t.val (op ⊤)) (N.unitHomEquiv.apply_symm_apply s)
  have h := congrArg
    (fun g : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ N =>
      g.val.app (op ⊤) (1 : Γ(X, ⊤))) hz
  change (N.unitHomEquiv.symm s).val.app (op ⊤) (1 : Γ(X, ⊤)) = 0 at h
  exact hs (heval.symm.trans h)

/-- Tensor the original section map to obtain the actual map out of H. -/
def twistMap (H : InvertibleSheaf X) (N : X.Modules) (s : N.sections) :
    H.obj ⟶ N ⊗ H.obj :=
  (leftStructureIso H).inv ≫ (tensorRight H.obj).map (N.unitHomEquiv.symm s)

/-- Faithfulness of the existing tensor equivalence preserves the original section's nonvanishing. -/
theorem twistMap_ne_zero (H : InvertibleSheaf X) (N : X.Modules) (s : N.sections)
    (hs : s.val (op ⊤) ≠ 0) : twistMap H N s ≠ 0 := by
  letI := tensorRight_faithful H
  letI := H.tensorRight_preservesZeroMorphisms
  intro hz
  have hmap : (tensorRight H.obj).map (N.unitHomEquiv.symm s) = 0 := by
    have h := congrArg (fun t : H.obj ⟶ N ⊗ H.obj => (leftStructureIso H).hom ≫ t) hz
    simpa only [twistMap, Category.assoc, Iso.hom_inv_id_assoc, comp_zero] using h
  apply sectionHom_ne_zero N s hs
  apply (tensorRight H.obj).map_injective
  rw [Functor.map_zero, hmap]

/-- An actual tensor representative gives a nonzero map to the specified original target. -/
theorem exists_nonzero_map (H : InvertibleSheaf X) (N P : X.Modules)
    (e : N ⊗ H.obj ≅ P) (s : N.sections) (hs : s.val (op ⊤) ≠ 0) :
    ∃ g : H.obj ⟶ P, g ≠ 0 := by
  refine ⟨twistMap H N s ≫ e.hom, ?_⟩
  intro hz
  apply twistMap_ne_zero H N s hs
  have h := congrArg (fun t : H.obj ⟶ P => t ≫ e.inv) hz
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp] using h

end KltDP.Geometry.InvertibleSectionTwistMap
