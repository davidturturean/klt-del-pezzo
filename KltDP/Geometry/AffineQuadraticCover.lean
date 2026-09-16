import KltDP.Geometry.QuadraticCoverRescaling
import KltDP.Geometry.QuadraticCoverBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Fiber

/-!
# The actual affine quadratic cover

The arbitrary-branch quotient defines an actual affine scheme and its canonical
morphism to `Spec R`. This morphism is finite and flat. Unit rescaling gives an
actual scheme isomorphism over `Spec R`. Actual affine base changes, including
the scheme-theoretic fiber at a point, are identified with quadratic quotients
whose branch coefficient is mapped through the original base-ring map.

No geometric degree, surjectivity, smoothness, integrality, global branch
section or line-bundle atlas is supplied as an assumption or inferred here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R : Type u} [CommRing R]

/-- The spectrum of the actual quadratic quotient. -/
def affineScheme (s : R) : Scheme := Spec (.of (CoverAlgebra s))

/-- The actual structural map induced by the quotient's base-algebra map. -/
def toBase (s : R) : affineScheme s ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (CoverAlgebra s)))

private theorem finite_algebraMap_iff (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : (algebraMap A B).Finite ↔ Module.Finite A B := by
  simp only [RingHom.Finite]
  congr!
  exact Algebra.algebra_ext _ _ fun _ => rfl

private theorem specMap_isFinite {A B : CommRingCat.{u}} (f : A ⟶ B)
    (hf : f.hom.Finite) : AlgebraicGeometry.IsFinite (Spec.map f) := by
  apply (HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.IsFinite)).mpr
  refine ⟨inferInstance, ?_⟩
  have H := RingHom.finite_respectsIso
  rw [← H.cancel_right_isIso _ (Scheme.ΓSpecIso _).hom,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
    H.cancel_left_isIso]
  exact hf

/-- Finiteness follows from the proved monic quotient module, on actual schemes. -/
theorem toBase_isFinite (s : R) : AlgebraicGeometry.IsFinite (toBase s) := by
  apply specMap_isFinite
  exact (finite_algebraMap_iff R (CoverAlgebra s)).mpr (finite s)

/-- Flatness follows from the actual free quotient module. -/
theorem toBase_flat (s : R) : AlgebraicGeometry.Flat (toBase s) := by
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)).mpr
  exact flat_algebraMap_iff.mpr (flat s)

/-- The contravariant scheme isomorphism induced by a unit generator change. -/
def rescaleSpecIso (s s' : R) (v : Rˣ) (h : s = (v : R) ^ 2 * s') :
    affineScheme s' ≅ affineScheme s :=
  Scheme.Spec.mapIso (rescaleEquiv s s' v h).toRingEquiv.toCommRingCatIso.op

/-- This specifies the actual coordinate-ring map, including the root rescaling. -/
theorem rescaleSpecIso_hom (s s' : R) (v : Rˣ) (h : s = (v : R) ^ 2 * s') :
    (rescaleSpecIso s s' v h).hom =
      Spec.map (CommRingCat.ofHom (rescaleEquiv s s' v h).toRingHom) := rfl

@[simp]
theorem rescaleSpecIso_preimage (s s' : R) (v : Rˣ)
    (h : s = (v : R) ^ 2 * s') :
    (Spec.preimage (rescaleSpecIso s s' v h).hom).hom =
      (rescaleEquiv s s' v h).toRingHom := by
  rw [rescaleSpecIso_hom, Spec.preimage_map]
  rfl

/-- The rescaling isomorphism is over the actual original base scheme. -/
@[reassoc]
theorem rescaleSpecIso_hom_toBase (s s' : R) (v : Rˣ)
    (h : s = (v : R) ^ 2 * s') :
    (rescaleSpecIso s s' v h).hom ≫ toBase s = toBase s' := by
  rw [rescaleSpecIso_hom]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (rescaleEquiv s s' v h).commutes r

@[reassoc]
theorem rescaleSpecIso_inv_toBase (s s' : R) (v : Rˣ)
    (h : s = (v : R) ^ 2 * s') :
    (rescaleSpecIso s s' v h).inv ≫ toBase s' = toBase s := by
  rw [← rescaleSpecIso_hom_toBase s s' v h, Iso.inv_hom_id_assoc]

section BaseChange

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Tensor factors are placed in the order used by the actual affine pullback. -/
def baseChangeTensorEquiv (s : R) :
    CoverAlgebra s ⊗[R] S ≃+* CoverAlgebra (algebraMap R S s) :=
  (Algebra.TensorProduct.comm R (CoverAlgebra s) S).toRingEquiv.trans
    (baseChangeEquiv (S := S) s).toRingEquiv

@[simp]
theorem baseChangeTensorEquiv_one_tmul (s : R) (r : S) :
    baseChangeTensorEquiv S s ((1 : CoverAlgebra s) ⊗ₜ[R] r) =
      algebraMap S (CoverAlgebra (algebraMap R S s)) r := by
  change baseChangeEquiv (S := S) s
    ((Algebra.TensorProduct.comm R (CoverAlgebra s) S)
      ((1 : CoverAlgebra s) ⊗ₜ[R] r)) = _
  rw [Algebra.TensorProduct.comm_tmul]
  change baseChangeEquiv (S := S) s
    (algebraMap S (S ⊗[R] CoverAlgebra s) r) = _
  exact (baseChangeEquiv (S := S) s).commutes r

@[simp]
theorem baseChangeTensorEquiv_root_tmul_one (s : R) :
    baseChangeTensorEquiv S s (root s ⊗ₜ[R] (1 : S)) =
      root (algebraMap R S s) := by
  change baseChangeEquiv (S := S) s
    ((Algebra.TensorProduct.comm R (CoverAlgebra s) S) (root s ⊗ₜ[R] (1 : S))) = _
  rw [Algebra.TensorProduct.comm_tmul, baseChangeEquiv_one_tmul_root]

/-- The actual affine base change is the quotient with the mapped branch coefficient. -/
def baseChangeSpecIso (s : R) :
    pullback (toBase s) (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≅
      affineScheme (algebraMap R S s) :=
  pullbackSpecIso R (CoverAlgebra s) S ≪≫
    Scheme.Spec.mapIso (baseChangeTensorEquiv S s).symm.toCommRingCatIso.op

/-- The quotient comparison preserves the actual map to the new base. -/
@[reassoc]
theorem baseChangeSpecIso_inv_snd (s : R) :
    (baseChangeSpecIso S s).inv ≫ pullback.snd _ _ = toBase (algebraMap R S s) := by
  change (Spec.map (CommRingCat.ofHom (baseChangeTensorEquiv S s).toRingHom) ≫
    (pullbackSpecIso R (CoverAlgebra s) S).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  change Spec.map _ = Spec.map _
  congr 1
  ext r
  exact baseChangeTensorEquiv_one_tmul S s r

@[reassoc]
theorem baseChangeSpecIso_hom_toBase (s : R) :
    (baseChangeSpecIso S s).hom ≫ toBase (algebraMap R S s) = pullback.snd _ _ := by
  rw [← baseChangeSpecIso_inv_snd S s, Iso.hom_inv_id_assoc]

end BaseChange

/-- The actual base-to-residue-field map, recovered from the canonical residue-field point. -/
def residueMap (x : Spec (CommRingCat.of R)) :
    R →+* (Spec (CommRingCat.of R)).residueField x :=
  (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField x)).hom

@[simp]
theorem residueMap_spec (x : Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (residueMap x)) =
      (Spec (CommRingCat.of R)).fromSpecResidueField x :=
  Spec.map_preimage _

/-- The actual scheme-theoretic fiber is the quadratic algebra over the actual residue field. -/
def fiberSpecIso (s : R) (x : Spec (CommRingCat.of R)) :
    (toBase s).fiber x ≅ affineScheme (residueMap x s) := by
  letI : Algebra R ((Spec (CommRingCat.of R)).residueField x) := (residueMap x).toAlgebra
  exact (pullback.congrHom rfl (residueMap_spec x).symm) ≪≫
    baseChangeSpecIso ((Spec (CommRingCat.of R)).residueField x) s

/-- The fiber comparison is over the original point's residue field. -/
@[reassoc]
theorem fiberSpecIso_hom_toBase (s : R) (x : Spec (CommRingCat.of R)) :
    (fiberSpecIso s x).hom ≫ toBase (residueMap x s) =
      (toBase s).fiberToSpecResidueField x := by
  letI : Algebra R ((Spec (CommRingCat.of R)).residueField x) := (residueMap x).toAlgebra
  change ((pullback.congrHom rfl (residueMap_spec x).symm).hom ≫
    (baseChangeSpecIso ((Spec (CommRingCat.of R)).residueField x) s).hom) ≫
      toBase (algebraMap R ((Spec (CommRingCat.of R)).residueField x) s) = pullback.snd _ _
  rw [Category.assoc, baseChangeSpecIso_hom_toBase]
  change (pullback.congrHom rfl (residueMap_spec x).symm).hom ≫
      pullback.snd (toBase s) (Spec.map (CommRingCat.ofHom (residueMap x))) =
    pullback.snd (toBase s) ((Spec (CommRingCat.of R)).fromSpecResidueField x)
  simp only [pullback.congrHom_hom, pullback.map]
  exact (pullback.lift_snd (f := toBase s)
    (g := Spec.map (CommRingCat.ofHom (residueMap x))) _ _ _).trans
      (Category.comp_id _)

/-- The actual structural map of every scheme-theoretic fiber is finite. -/
theorem fiberToSpec_isFinite (s : R) (x : Spec (CommRingCat.of R)) :
    AlgebraicGeometry.IsFinite ((toBase s).fiberToSpecResidueField x) := by
  letI := toBase_isFinite s
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- Flatness is retained by the actual scheme-theoretic fiber map. -/
theorem fiberToSpec_flat (s : R) (x : Spec (CommRingCat.of R)) :
    AlgebraicGeometry.Flat ((toBase s).fiberToSpecResidueField x) := by
  letI := toBase_flat s
  change AlgebraicGeometry.Flat (pullback.snd (toBase s)
    ((Spec (CommRingCat.of R)).fromSpecResidueField x))
  infer_instance

/-- Every actual fiber algebra has dimension two over the point's residue field. -/
theorem fiber_algebra_finrank (s : R) (x : Spec (CommRingCat.of R)) :
    Module.finrank ((Spec (CommRingCat.of R)).residueField x)
      (CoverAlgebra (residueMap x s)) = 2 :=
  finrank (residueMap x s)

end KltDP.Geometry.QuadraticCover
