import KltDP.Geometry.ModuleCohomologyEuler
import Mathlib.LinearAlgebra.Dimension.Basic

/-! Changing the base field by an actual field isomorphism preserves
all native cohomology dimensions and the native Euler value. The scalar
compatibility is proved from the original Gamma-Spec naturality; no
cohomology comparison or arbitrary module action is assumed. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k l : Type u} [Field k] [Field l] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of l))

/-- The original scalar map for a composite with Spec of a field map. -/
theorem baseFieldToGlobalSections_comp_specMap (φ : k →+* l) (a : k) :
    baseFieldToGlobalSections (f ≫ Spec.map (CommRingCat.ofHom φ)) a =
      baseFieldToGlobalSections f (φ a) := by
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) a
  change (Scheme.ΓSpecIso (CommRingCat.of l)).inv (φ a) =
    (Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a) at h
  exact congrArg (fun z : Γ(Spec (CommRingCat.of l), ⊤) => f.appTop z) h.symm

/-- Every actual cohomology dimension is unchanged by the original field iso. -/
theorem cohomologyDimension_comp_specIso (e : k ≃+* l) (M : X.Modules) (n : ℕ) :
    cohomologyDimension (f ≫ Spec.map e.toCommRingCatIso.hom) M n =
      cohomologyDimension f M n := by
  letI := baseModule (f ≫ Spec.map e.toCommRingCatIso.hom) M n
  letI := baseModule f M n
  have h : Module.rank k (H M n) = Module.rank l (H M n) := by
    apply rank_eq_of_equiv_equiv (e : k → l) (AddEquiv.refl (H M n)) e.bijective
    intro a x
    change (zariskiFunctor X n).map
      (globalSmulHom M (baseFieldToGlobalSections
        (f ≫ Spec.map e.toCommRingCatIso.hom) a)) x =
      (zariskiFunctor X n).map
        (globalSmulHom M (baseFieldToGlobalSections f (e a))) x
    have hscalar := baseFieldToGlobalSections_comp_specMap f e.toRingHom a
    exact congrArg (fun z : Γ(X, ⊤) =>
      (zariskiFunctor X n).map (globalSmulHom M z) x) hscalar
  change (Module.rank k (H M n)).toNat = (Module.rank l (H M n)).toNat
  exact congrArg Cardinal.toNat h

/-- The original Euler characteristic is invariant under a base field iso. -/
theorem eulerCharacteristic_comp_specIso (e : k ≃+* l) (M : X.Modules) :
    eulerCharacteristic (f ≫ Spec.map e.toCommRingCatIso.hom) M =
      eulerCharacteristic f M := by
  unfold eulerCharacteristic
  apply finsum_congr
  intro n
  rw [cohomologyDimension_comp_specIso]

end KltDP.Geometry.ModuleCohomology

#check @KltDP.Geometry.ModuleCohomology.eulerCharacteristic_comp_specIso
#print axioms KltDP.Geometry.ModuleCohomology.eulerCharacteristic_comp_specIso
