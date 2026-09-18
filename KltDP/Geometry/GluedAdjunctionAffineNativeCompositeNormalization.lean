import KltDP.Geometry.GluedAdjunctionAffineProjectedFactorNormalization

/-!
# The two original affine maps after the native forward isomorphism

Check each original equation against its own factor independently, retaining
its inferred Hom carrier. Both results then meet at the same literal
original differential arrow. Final cancellation is a separate consumer.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionAffineNativeCompositeNormalization

private theorem stored_triangle {C : Type*} [Category C] {S T P : C}
    {e : T ≅ P} {y : S ⟶ T} {m : S ⟶ P}
    (hy : y = m ≫ e.inv) : y ≫ e.hom = m := by
  rw [hy]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original affine map's native forward composite is the original differential arrow. -/
def native_forward_composite_heq {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    (heq_of_eq
      (GluedAdjunctionOriginalAffineNormalization.nativeForwardTriangle f U hSmooth)).trans
      (GluedAdjunctionAffineProjectedFactorNormalization.native_forward_factor_heq f U)

/-- The stored map's native forward composite meets the same original differential arrow. -/
def native_stored_composite_heq {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    (heq_of_eq (stored_triangle
      (GluedAdjunctionOriginalAffineNormalization.nativeStoredEquation f U hSmooth))).trans
      (GluedAdjunctionAffineProjectedFactorNormalization.native_stored_factor_heq f U)

/-- Compare only the original native forward composites, without cancelling or recasting them. -/
def native_composites_heq {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    (native_forward_composite_heq f U hSmooth).trans
      (native_stored_composite_heq f U hSmooth).symm

end KltDP.Geometry.GluedAdjunctionAffineNativeCompositeNormalization
