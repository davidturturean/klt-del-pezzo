import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual affine square of an extended quotient ideal

If J is the extension of I along the original ring map, the original
quotient map Spec(S/J) → Spec(R/I) is its actual scheme base change.
The proof retains both projections of the pinned tensor-product pullback.

Reuse: `quotIdealMapEquivTensorQuot` and `pullbackSpecIso`, as in the
existing AffineBlowupFiber, ExtendedIdealFiber and QuadraticBranchFiber.
Official newer Mathlib at 80cbd0498ab39e21d24d6730b3f932cec672a702,
RingTheory/TensorProduct/Quotient.lean:31-60 (Apache 2.0), has the same
tensor quotient and representative formulas. No newer source is ported.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace KltDP.QuotientIdealPullback

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original quotient square of an extended ideal is a categorical pullback. -/
theorem isPullback (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (h : Ideal.map f I = J) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp (le_of_eq h)))))
      (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  letI : Algebra R S := f.toAlgebra
  let e : (S ⧸ J) ≃+* S ⊗[R] (R ⧸ I) :=
    (Ideal.quotEquivOfEq h.symm).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toRingEquiv
  have he (a : S) : e (Ideal.Quotient.mk J a) = a ⊗ₜ[R] (1 : R ⧸ I) := by
    change Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I
      (Ideal.quotEquivOfEq h.symm (Ideal.Quotient.mk J a)) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk S I a
  have he' (a : S) (r : R) :
      e.symm (a ⊗ₜ[R] (Ideal.Quotient.mk I r)) =
        Ideal.Quotient.mk J (f r * a) := by
    change (Ideal.quotEquivOfEq h.symm).symm
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
        (a ⊗ₜ[R] (Ideal.Quotient.mk I r))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
      Algebra.smul_def, Ideal.quotEquivOfEq_symm,
      Ideal.Quotient.mk_eq_mk]
    change Ideal.quotEquivOfEq h (Ideal.Quotient.mk (Ideal.map f I) (f r * a)) =
      Ideal.Quotient.mk J (f r * a)
    exact Ideal.quotEquivOfEq_mk h (f r * a)
  let q := Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp (le_of_eq h))
  let iso : Spec (.of (S ⧸ J)) ≅
      pullback (Spec.map (CommRingCat.ofHom f))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    Scheme.Spec.mapIso e.symm.toCommRingCatIso.op ≪≫
      (pullbackSpecIso R S (R ⧸ I)).symm
  have hf : iso.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    change (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      (pullbackSpecIso R S (R ⧸ I)).inv) ≫ pullback.fst _ _ = _
    rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
    apply congrArg (fun k : S →+* (S ⧸ J) => Spec.map (CommRingCat.ofHom k))
    apply RingHom.ext
    intro a
    change e.symm (a ⊗ₜ[R] (1 : R ⧸ I)) = _
    apply e.injective
    rw [RingEquiv.apply_symm_apply, he]
  have hg : iso.hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom q) := by
    change (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      (pullbackSpecIso R S (R ⧸ I)).inv) ≫ pullback.snd _ _ = _
    rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
    apply congrArg (fun k : (R ⧸ I) →+* (S ⧸ J) => Spec.map (CommRingCat.ofHom k))
    apply RingHom.ext
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change e.symm ((1 : S) ⊗ₜ[R] (Ideal.Quotient.mk I r)) = Ideal.Quotient.mk J (f r)
    rw [he', mul_one]
  apply IsPullback.of_iso_pullback _ iso hf hg
  constructor
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end KltDP.QuotientIdealPullback
