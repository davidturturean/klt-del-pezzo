import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Affine intersection of two closed subschemes

For ideals `I, J` of a commutative ring `A`, the fibre product of the closed
subschemes `Spec (A ⧸ I)` and `Spec (A ⧸ J)` over `Spec A` is `Spec (A ⧸ (I ⊔ J))`:
the pinned `pullbackSpecIso` identifies the fibre product with the spectrum of
`(A ⧸ I) ⊗[A] (A ⧸ J)`, and the tensor product of two quotients is the quotient by
the sum of the ideals. This is the affine-local content of "the intersection of two
closed subschemes is cut out by both equations".

Gluing this identification to the global intersection subscheme of a prime curve
and an effective Cartier divisor is a recorded obligation (see
`F03_RESTRICTION_ADAPTERS.md`); nothing global is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace KltDP.Geometry

variable {A : Type u} [CommRing A] (I J : Ideal A)

/-- `(A ⧸ I) ⊗[A] (A ⧸ J) ≃ A ⧸ (I ⊔ J)` as rings. -/
def quotientTensorQuotientRingEquiv : (A ⧸ I) ⊗[A] (A ⧸ J) ≃+* A ⧸ (I ⊔ J) :=
  (((Algebra.TensorProduct.comm A (A ⧸ I) (A ⧸ J)).toRingEquiv.trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ J) I).symm.toRingEquiv).trans
    (Ideal.quotEquivOfEq (by rw [Ideal.Quotient.algebraMap_eq]))).trans
    ((DoubleQuot.quotQuotEquivQuotSup J I).trans (Ideal.quotEquivOfEq (sup_comm J I)))

/-- The fibre product of `Spec (A ⧸ I)` and `Spec (A ⧸ J)` over `Spec A` is
`Spec (A ⧸ (I ⊔ J))`. -/
def specQuotientPullbackIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
        (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ J)))) ≅
      Spec (CommRingCat.of (A ⧸ (I ⊔ J))) :=
  pullbackSpecIso A (A ⧸ I) (A ⧸ J) ≪≫
    { hom := Spec.map (quotientTensorQuotientRingEquiv I J).toCommRingCatIso.inv
      inv := Spec.map (quotientTensorQuotientRingEquiv I J).toCommRingCatIso.hom
      hom_inv_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
      inv_hom_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id] }

end KltDP.Geometry
