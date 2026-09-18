import KltDP.Geometry.QuadraticCoverAppLE

/-!
# Actual pushforward sections on the original quadratic charts

The original chart inclusions identify functions on each inverse-image
open with the original quadratic quotient algebra. The comparison follows
the actual restriction and frame maps, including for nested charts with
different frames. These are the section maps used by global module descent;
no abstract rank-two algebra or global splitting is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover

variable {X : Scheme.{u}} {ι : Type u} (D : QuadraticCoverAtlas.Data X ι)

/-- A map between two nested original charts retains their common map
into the unchanged glued cover. -/
@[reassoc]
theorem nestedChart_map_chartι (i j : ι) (hij : D.opens i ≤ D.opens j) :
    D.map (le_refl (D.opens j)) (le_refl (D.opens i)) hij ≫ D.chartι j = D.chartι i := by
  let a := D.map (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
    (le_refl (D.opens i)) (le_inf le_rfl hij)
  have h := congrArg (fun f : D.overlap i j ⟶ D.scheme => a ≫ f)
    (QuadraticCoverAppLE.direct_overlap_chart D i j)
  simpa only [a, ← Category.assoc, overlapToChart, map_comp, map_self,
    Category.id_comp] using h

/-- The whole original chart lies over its original base open. -/
theorem top_le_chart_preimage (i : ι) :
    ⊤ ≤ D.chartι i ⁻¹ᵁ (D.morphism ⁻¹ᵁ D.opens i) := by
  intro x _
  change (D.chartι i ≫ D.morphism).base x ∈ D.opens i
  rw [D.chartι_morphism]
  exact D.frameToBase_mem (le_refl (D.opens i)) (D.affine i) x

/-- Restriction of original cover functions to the original affine chart. -/
def pushforwardChartSectionMap (i : ι) :
    Γ(D.scheme, D.morphism ⁻¹ᵁ D.opens i) ⟶ Γ(D.chart i, ⊤) :=
  (D.chartι i).appLE _ ⊤ (D.top_le_chart_preimage i)

instance pushforwardChartSectionMap_isIso (i : ι) :
    IsIso (D.pushforwardChartSectionMap i) := by
  have himage : D.chartι i ''ᵁ ⊤ = D.morphism ⁻¹ᵁ D.opens i := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact TopologicalSpace.Opens.ext (D.range_chartι i)
  unfold pushforwardChartSectionMap
  apply ((D.chartι i).appLE_congr (D.top_le_chart_preimage i) himage.symm rfl
    (fun {_ _} f => IsIso f)).mpr
  rw [← Scheme.Hom.appIso_hom']
  infer_instance

/-- Functions on the actual inverse-image open are the actual quotient algebra. -/
def pushforwardChartAlgebraIso (i : ι) :
    Γ(D.scheme, D.morphism ⁻¹ᵁ D.opens i) ≅
      CommRingCat.of (CoverAlgebra (res X (le_refl (D.opens i)) (D.sections i))) :=
  asIso (D.pushforwardChartSectionMap i) ≪≫ Scheme.ΓSpecIso _

/-- Original chart restriction commutes with the actual nested frame map. -/
theorem pushforwardChartSectionMap_restrict (i j : ι) (hij : D.opens i ≤ D.opens j)
    (s : Γ(D.scheme, D.morphism ⁻¹ᵁ D.opens j)) :
    (D.map (le_refl (D.opens j)) (le_refl (D.opens i)) hij).appTop
        (D.pushforwardChartSectionMap j s) =
      D.pushforwardChartSectionMap i
        (res D.scheme (D.morphism.preimage_le_preimage_of_le hij) s) := by
  have hcomp := ConcreteCategory.congr_hom (Scheme.appLE_comp_appLE
    (D.map (le_refl (D.opens j)) (le_refl (D.opens i)) hij) (D.chartι j)
    (D.morphism ⁻¹ᵁ D.opens j) ⊤ ⊤ (D.top_le_chart_preimage j) le_rfl) s
  simp only [D.nestedChart_map_chartι i j hij] at hcomp
  have hres := QuadraticCoverAppLE.appLE_res (D.chartι i)
    (D.morphism.preimage_le_preimage_of_le hij) (D.top_le_chart_preimage i) s
  exact hcomp.trans hres.symm

/-- The actual affine quotient identification retains the original
ring homomorphism on every nested overlap. -/
theorem pushforwardChartAlgebraIso_restrict (i j : ι) (hij : D.opens i ≤ D.opens j)
    (s : Γ(D.scheme, D.morphism ⁻¹ᵁ D.opens j)) :
    (D.pushforwardChartAlgebraIso i).hom
        (res D.scheme (D.morphism.preimage_le_preimage_of_le hij) s) =
      Spec.preimage (D.map (le_refl (D.opens j)) (le_refl (D.opens i)) hij)
        ((D.pushforwardChartAlgebraIso j).hom s) := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality
    (Spec.preimage (D.map (le_refl (D.opens j)) (le_refl (D.opens i)) hij)))
      (D.pushforwardChartSectionMap j s)
  rw [Spec.map_preimage] at h
  change (Scheme.ΓSpecIso (CommRingCat.of
      (CoverAlgebra (res X (le_refl (D.opens i)) (D.sections i))))).hom
      ((D.map (le_refl (D.opens j)) (le_refl (D.opens i)) hij).appTop
        (D.pushforwardChartSectionMap j s)) =
    Spec.preimage (D.map (le_refl (D.opens j)) (le_refl (D.opens i)) hij)
      ((Scheme.ΓSpecIso (CommRingCat.of
        (CoverAlgebra (res X (le_refl (D.opens j)) (D.sections j))))).hom
          (D.pushforwardChartSectionMap j s)) at h
  rw [D.pushforwardChartSectionMap_restrict i j hij] at h
  exact h

end KltDP.Geometry.QuadraticCoverAtlas.Data

#check @KltDP.Geometry.QuadraticCoverAtlas.Data.pushforwardChartAlgebraIso_restrict
#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.pushforwardChartAlgebraIso_restrict
