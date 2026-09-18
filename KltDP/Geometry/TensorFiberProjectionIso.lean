import Mathlib.AlgebraicGeometry.Pullbacks

/-! Keep the pinned tensor inclusion literal through the actual Spec
pullback comparison. No scalar-map definition is expanded inside Spec. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

namespace KltDP.Geometry.TensorFiberProjectionIso

/-- Reordering the original categorical fiber retains an isomorphic
projection to the original field spectrum. -/
theorem fst_isIso (R A K : Type u) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K]
    [IsIso (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    IsIso (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := by
  rw [← pullbackSymmetry_inv_comp_snd
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))]
  infer_instance

/-- The pinned pullbackSpecIso identifies the original projection with
the spectrum of the literal left tensor inclusion. -/
theorem includeLeft_spec_isIso (R A K : Type u) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K]
    [IsIso (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    IsIso (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A))) := by
  letI := fst_isIso R A K
  rw [← pullbackSpecIso_inv_fst R K A]
  infer_instance

#check KltDP.Geometry.TensorFiberProjectionIso.includeLeft_spec_isIso
#print axioms KltDP.Geometry.TensorFiberProjectionIso.fst_isIso
#print axioms KltDP.Geometry.TensorFiberProjectionIso.includeLeft_spec_isIso

end KltDP.Geometry.TensorFiberProjectionIso
