import KltDP.Geometry.QuadraticCoverAtlasGluing

/-!
# Original section maps used in quadratic base-change overlaps

These pointwise adapters are the pinned naturality and restriction identities
for `Scheme.Hom.appLE`, exposed with the actual section-ring homomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QuadraticCoverAppLE

open TransitionUnitGluing

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Restricting after the actual section map is its actual smaller-open map. -/
theorem res_appLE {U : X.Opens} {V W : Y.Opens}
    (hVU : V ≤ f ⁻¹ᵁ U) (hWV : W ≤ V) (s : Γ(X, U)) :
    res Y hWV (f.appLE U V hVU s) = f.appLE U W (hWV.trans hVU) s :=
  ConcreteCategory.congr_hom (f.appLE_map hVU (homOfLE hWV).op) s

/-- Mapping an original restriction equals the original larger-open section map. -/
theorem appLE_res {U T : X.Opens} {V : Y.Opens}
    (hUT : U ≤ T) (hVU : V ≤ f ⁻¹ᵁ U) (s : Γ(X, T)) :
    f.appLE U V hVU (res X hUT s) =
      f.appLE T V (hVU.trans (f.preimage_le_preimage_of_le hUT)) s :=
  ConcreteCategory.congr_hom (f.map_appLE hVU (homOfLE hUT).op) s

/-- The two original coefficient-ring paths around an affine restriction square agree. -/
theorem restriction_square {U T : X.Opens} {V W : Y.Opens}
    (hUT : U ≤ T) (hVU : V ≤ f ⁻¹ᵁ U) (hWT : W ≤ f ⁻¹ᵁ T) (hVW : V ≤ W) :
    (f.appLE U V hVU).hom.comp (res X hUT) =
      (res Y hVW).comp (f.appLE T W hWT).hom := by
  ext s
  exact (appLE_res f hUT hVU s).trans (res_appLE f hWT hVW s).symm

/-- Original direct overlap maps have the same actual glued chart image. -/
theorem direct_overlap_chart {ι : Type u} (D : QuadraticCoverAtlas.Data X ι) (i j : ι) :
    D.map (le_refl (D.opens j)) (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
      inf_le_right ≫ D.chartι j = D.overlapToChart i j ≫ D.chartι i := by
  have h := D.glueData.glue_condition i j
  change D.transition i j ≫ D.overlapToChart j i ≫ D.chartι j =
    D.overlapToChart i j ≫ D.chartι i at h
  rw [← Category.assoc] at h
  simpa only [QuadraticCoverAtlas.Data.transition, QuadraticCoverAtlas.Data.overlapToChart,
    QuadraticCoverAtlas.Data.map_comp] using h

#print axioms restriction_square

end KltDP.Geometry.QuadraticCoverAppLE
