import KltDP.Geometry.LinearSystemNonvanishingPreimage
import KltDP.Geometry.ProjectiveCoordinateSectionBasicOpen
import KltDP.Geometry.AffineOpenModuleDenominators

/-!
# Original projective coordinates pull back to the normalized section coefficients

The original affine chart square determines its original ring map through
the canonical Gamma--Spec isomorphisms. Applying this to the glued linear
system morphism computes its appLE on every actual coordinate fraction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemMorphism

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] MvPolynomial.gradedAlgebra

open InvertibleSectionNonvanishingOpen ProjectiveCoordinateSectionBasicOpen ProjectiveChart

private theorem appLE_ringMap_of_chart_square {A : CommRingCat.{u}}
    {X Y : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (g : X ⟶ Y)
    (V : Y.Opens) (q : Spec A ⟶ Y) (hq : ⊤ ≤ q ⁻¹ᵁ V)
    (e : A ⟶ Γ(Y, V))
    (he : e ≫ q.appLE V ⊤ hq = (Scheme.ΓSpecIso A).inv)
    (φ : A ⟶ Γ(X, U)) (hsq : hU.fromSpec ≫ g = Spec.map φ ≫ q)
    (hUV : U ≤ g ⁻¹ᵁ V) : e ≫ g.appLE V U hUV = φ := by
  let hf : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have hfrom : hU.fromSpec.appLE U ⊤ hf = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    simpa only [homOfLE_refl, op_id, Functor.map_id, Category.comp_id] using
      AffineOpenModule.fromSpec_appLE hU ⊤ hf
  have hcomp : g.appLE V U hUV ≫ hU.fromSpec.appLE U ⊤ hf =
      q.appLE V ⊤ hq ≫ (Spec.map φ).appTop := by
    rw [Scheme.appLE_comp_appLE,
      ProjectiveLineCanonicalFrame.appLE_of_eq hsq.symm,
      ← Scheme.appLE_comp_appLE (Spec.map φ) q V ⊤ ⊤ hq le_top]
    exact congrArg (fun α => q.appLE V ⊤ hq ≫ α)
      (Scheme.Hom.appLE_eq_app (Spec.map φ) (U := ⊤))
  apply (cancel_mono (Scheme.ΓSpecIso Γ(X, U)).inv).mp
  calc
    (e ≫ g.appLE V U hUV) ≫ (Scheme.ΓSpecIso Γ(X, U)).inv =
        e ≫ (g.appLE V U hUV ≫ hU.fromSpec.appLE U ⊤ hf) := by
      rw [hfrom, Category.assoc]
    _ = e ≫ (q.appLE V ⊤ hq ≫ (Spec.map φ).appTop) :=
      congrArg (fun a => e ≫ a) hcomp
    _ = (Scheme.ΓSpecIso A).inv ≫ (Spec.map φ).appTop := by
      rw [← Category.assoc, he]
    _ = φ ≫ (Scheme.ΓSpecIso Γ(X, U)).inv := (Scheme.ΓSpecIso_inv_naturality φ).symm

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  {n : ℕ} (s : Fin (n + 1) → L.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

/-- The original source chart maps into its selected standard projective chart. -/
theorem chart_le_preimage_standardOpen (c : Chart L s) :
    c.affineOpen.1 ≤ morphism L s f hcover ⁻¹ᵁ standardOpen k n c.index := by
  have hstd : (ProjectiveChart.coordinateChartMorphism k n c.index).opensRange =
      standardOpen k n c.index := ProjectiveChart.coordinateChartMorphism_opensRange k n c.index
  rw [← hstd, morphism_preimage_coordinateChart]
  exact c.nonvanishing

/-- The actual morphism sends each original projective coordinate fraction
to the original normalized coefficient on the specified affine source chart. -/
theorem morphism_appLE_coordinateSection (c : Chart L s)
    (hc : c.affineOpen.1 ≤ morphism L s f hcover ⁻¹ᵁ standardOpen k n c.index)
    (j : Fin (n + 1)) :
    (morphism L s f hcover).appLE (standardOpen k n c.index) c.affineOpen.1 hc
        (coordinateSection k n c.index j) =
      coordinates L s c.frame c.inFrame c.index c.nonvanishing j := by
  let r := coordinates L s c.frame c.inFrame c.index c.nonvanishing
  let a := (baseToAffineSectionsMap f c.affineOpen.2).hom
  let hm : r c.index = 1 := coordinates_self L s c.frame c.inFrame c.index c.nonvanishing
  let φ : CommRingCat.of (coordinateChartRing k n c.index) ⟶ Γ(X, c.affineOpen.1) :=
    CommRingCat.ofHom (ProjectiveChart.tupleChartHom n a r c.index hm)
  have ht : ⊤ ≤ ProjectiveChart.coordinateChartMorphism k n c.index ⁻¹ᵁ
      standardOpen k n c.index := by
    intro x _
    change (ProjectiveChart.coordinateChartMorphism k n c.index).base x ∈
      Proj.basicOpen (grading k n) (MvPolynomial.X c.index)
    rw [← ProjectiveChart.coordinateChartMorphism_opensRange]
    exact Set.mem_range_self x
  have he := appLE_ringMap_of_chart_square c.affineOpen.2 (morphism L s f hcover)
    (standardOpen k n c.index) (ProjectiveChart.coordinateChartMorphism k n c.index) ht
    (Proj.awayToSection (grading k n) (MvPolynomial.X c.index))
    (ProjectiveLineCanonicalFrame.awayToSection_awayι_appLE
      (grading k n) (ProjectiveChart.coordinate_mem k n c.index) Nat.one_pos ht)
    φ (chart_morphism L s f hcover c) hc
  exact (ConcreteCategory.congr_hom he (ProjectiveChart.chartFraction k n c.index j)).trans
    (ProjectiveChart.tupleChartHom_chartFraction n a r c.index hm j)

end KltDP.Geometry.LinearSystemMorphism
