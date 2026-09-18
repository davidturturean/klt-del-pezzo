import KltDP.Geometry.ProjectiveSpaceCoordinateCharts
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FiniteType

/-!
# An original finite-type affine scheme embeds in a projective coordinate chart

The pinned finite-type polynomial quotient theorem supplies an actual finite
closed affine embedding. The existing dehomogenization isomorphism identifies
its ambient affine space with the original first projective coordinate chart.
The constructed embedding preserves the original morphism to the base field.
No embedding, completion, or compatibility witness is a caller hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineFiniteTypeProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

open ProjectiveChart

/-- The first projective chart retains the original coefficient-field map. -/
theorem chartMorphism_comp_toSpec (k : Type u) [Field k] (n : ℕ) :
    chartMorphism k n ≫ projectiveSpaceToSpec k n =
      Spec.map (CommRingCat.ofHom (constants k n)) :=
  coordinateChartMorphism_over_base k n 0

/-- The finite-type algebra for the actual base map gives a closed embedding
of its spectrum into an actual projective coordinate chart over that map. -/
theorem exists_closed_chart_of_finiteType {k R : Type u} [Field k] [CommRing R]
    (c : k →+* R) (hc : c.FiniteType) :
    ∃ (n : ℕ) (i : Spec (CommRingCat.of R) ⟶
        Spec (CommRingCat.of (chartRing k n))),
      IsClosedImmersion i ∧
      i ≫ chartMorphism k n ≫ projectiveSpaceToSpec k n =
        Spec.map (CommRingCat.ofHom c) := by
  letI : Algebra k R := c.toAlgebra
  letI : Algebra.FiniteType k R := hc
  obtain ⟨n, a, ha⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
    (inferInstance : Algebra.FiniteType k R)
  let φ : chartRing k n →+* R :=
    a.toRingHom.comp (coordinateRingEquiv k n).toRingHom
  have hφ : Function.Surjective φ := ha.comp (coordinateRingEquiv k n).surjective
  have hconst : φ.comp (constants k n) = c := by
    ext r
    change a (coordinateRingEquiv k n (constants k n r)) = c r
    rw [coordinateRingEquiv_constants]
    exact a.commutes r
  refine ⟨n, Spec.map (CommRingCat.ofHom φ),
    IsClosedImmersion.spec_of_surjective _ hφ, ?_⟩
  rw [chartMorphism_comp_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hconst]

/-- An affine scheme of finite type for its original structure morphism
has an actual closed embedding in a projective chart over the same field. -/
theorem exists_closed_chart {k : Type u} [Field k] {W : Scheme.{u}} [IsAffine W]
    (σ : W ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ] :
    ∃ (n : ℕ) (i : W ⟶ Spec (CommRingCat.of (chartRing k n))),
      IsClosedImmersion i ∧
      i ≫ chartMorphism k n ≫ projectiveSpaceToSpec k n = σ := by
  let c : CommRingCat.of k ⟶ Γ(W, ⊤) := Spec.preimage (W.isoSpec.inv ≫ σ)
  have hc : c.hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    change LocallyOfFiniteType (Spec.map c)
    dsimp only [c]
    rw [Spec.map_preimage]
    infer_instance
  obtain ⟨n, i, hi, hbase⟩ := exists_closed_chart_of_finiteType c.hom hc
  letI : IsClosedImmersion i := hi
  refine ⟨n, W.isoSpec.hom ≫ i, inferInstance, ?_⟩
  rw [Category.assoc, hbase, CommRingCat.ofHom_hom]
  dsimp only [c]
  rw [Spec.map_preimage, Iso.hom_inv_id_assoc]

end KltDP.Geometry.AffineFiniteTypeProjectiveChart
