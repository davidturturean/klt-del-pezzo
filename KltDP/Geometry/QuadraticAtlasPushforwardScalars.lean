import KltDP.Geometry.QuadraticAtlasPushforwardCharts
import KltDP.Geometry.SchemeModulePushforwardScalars

/-!
# Original base scalars in the quadratic pushforward charts

The section isomorphism sends the original morphism's scalar action to
the original algebra map into the quadratic quotient. Thus it is a linear
equivalence for the actual pushforward module, not just a ring equivalence
between two otherwise unrelated section rings.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

private theorem fromSpec_appLE_self {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge =
      (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← CategoryTheory.Functor.map_comp]
  have h : (eqToHom hU.fromSpec_preimage_self).op ≫
      (homOfLE hU.fromSpec_preimage_self.ge).op = 𝟙 (op (⊤ : (Spec Γ(X, U)).Opens)) :=
    Subsingleton.elim _ _
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem top_le_chartToBase_preimage (i : ι) :
    ⊤ ≤ D.chartToBase i ⁻¹ᵁ D.opens i := by
  intro x _
  exact D.frameToBase_mem (le_refl (D.opens i)) (D.affine i) x

/-- The original structural sheaf homomorphism is the quotient algebra's
original scalar map under the actual inverse-image section comparison. -/
theorem pushforwardChartAlgebraIso_scalars (i : ι) :
    D.morphism.app (D.opens i) ≫ (D.pushforwardChartAlgebraIso i).hom =
      CommRingCat.ofHom (algebraMap Γ(X, D.opens i)
        (CoverAlgebra (res X (le_refl (D.opens i)) (D.sections i)))) := by
  have hc : D.morphism.app (D.opens i) ≫ D.pushforwardChartSectionMap i =
      (D.chartToBase i).appLE (D.opens i) ⊤ (D.top_le_chartToBase_preimage i) := by
    rw [pushforwardChartSectionMap, ← Scheme.comp_appLE]
    simp only [D.chartι_morphism]
  have hb := Scheme.appLE_comp_appLE
    (toBase (res X (le_refl (D.opens i)) (D.sections i))) (D.affine i).fromSpec
    (D.opens i) ⊤ ⊤ (D.affine i).fromSpec_preimage_self.ge le_rfl
  rw [fromSpec_appLE_self] at hb
  change D.morphism.app (D.opens i) ≫
    (D.pushforwardChartSectionMap i ≫ (Scheme.ΓSpecIso _).hom) = _
  rw [← Category.assoc, hc, ← hb]
  change ((Scheme.ΓSpecIso Γ(X, D.opens i)).inv ≫
    (toBase (res X (le_refl (D.opens i)) (D.sections i))).appTop) ≫
      (Scheme.ΓSpecIso _).hom = _
  rw [Category.assoc]
  unfold toBase
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- The actual original pushforward of the structure-sheaf module. -/
abbrev pushforwardUnit : X.Modules :=
  (schemeModulePushforward D.morphism).obj
    (_root_.SheafOfModules.unit D.scheme.ringCatSheaf)

/-- The chart equivalence preserves the original pushforward scalar action. -/
def pushforwardChartLinearEquiv (i : ι) :
    (D.pushforwardUnit).val.obj (op (D.opens i)) ≃ₗ[Γ(X, D.opens i)]
      CoverAlgebra (res X (le_refl (D.opens i)) (D.sections i)) :=
  { (D.pushforwardChartAlgebraIso i).commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' := by
      intro a s
      change Γ(D.scheme, D.morphism ⁻¹ᵁ D.opens i) at s
      change (D.pushforwardChartAlgebraIso i).hom (D.morphism.app (D.opens i) a * s) =
        a • (D.pushforwardChartAlgebraIso i).hom s
      rw [Algebra.smul_def, map_mul]
      exact congrArg (fun z => z * (D.pushforwardChartAlgebraIso i).hom s)
        (ConcreteCategory.congr_hom (D.pushforwardChartAlgebraIso_scalars i) a) }

end KltDP.Geometry.QuadraticCoverAtlas.Data

#check @KltDP.Geometry.QuadraticCoverAtlas.Data.pushforwardChartLinearEquiv
#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.pushforwardChartLinearEquiv
