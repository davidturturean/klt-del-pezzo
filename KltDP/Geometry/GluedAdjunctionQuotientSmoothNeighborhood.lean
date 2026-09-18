import KltDP.Geometry.SchemeSmoothPrincipalLocalization
import KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra

/-!
# Standard smooth quotient charts on the original ambient basic opens

Smoothness of the original closed subscheme restricts along its actual
quotient-chart inclusion. A principal neighborhood in that original
quotient ring lifts to an ambient section. The existing localization
comparison then proves standard smoothness of the original smaller
quotient section ring, with its original base algebra.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionQuotientSmoothNeighborhood

open GluedAdjunctionBasicOpenAlgebra GluedConormalBasicOpenLocalization

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData) (U : X.affineOpens)

/-- Original closed-scheme smoothness restricts to its actual quotient chart. -/
theorem quotient_chart_smooth [IsSmoothOfRelativeDimension 1 (I.gluedTo ≫ f)] :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    IsSmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ(X, U.1) ⧸ I.ideal U)))) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  have hComp := isSmoothOfRelativeDimension_comp (n := 0) (m := 1)
    (f := I.glueData.ι U) (g := I.gluedTo ≫ f)
  simpa only [Nat.zero_add, GluedChartKaehlerPullback.chartBaseMap_comp f I U] using hComp

/-- The lifted section cuts out precisely the original quotient principal open. -/
theorem chart_point_basicOpen_iff (r : Γ(X, U.1))
    (x : PrimeSpectrum (Γ(X, U.1) ⧸ I.ideal U)) :
    (I.glueData.ι U ≫ I.gluedTo).base x ∈ X.basicOpen r ↔
      Ideal.Quotient.mk (I.ideal U) r ∉ x.asIdeal := by
  change x ∈ (I.glueData.ι U ≫ I.gluedTo) ⁻¹ᵁ X.basicOpen r ↔ _
  rw [I.ι_gluedTo U, I.glueDataObjι_ι U, Scheme.preimage_comp,
    U.2.fromSpec_preimage_basicOpen]
  rfl

/-- Every point of an original quotient chart lies on an ambient basic open
whose original quotient section ring is standard smooth of dimension one. -/
theorem exists_basicOpen [IsSmoothOfRelativeDimension 1 (I.gluedTo ≫ f)]
    (x : PrimeSpectrum (Γ(X, U.1) ⧸ I.ideal U)) :
    ∃ r : Γ(X, U.1), (I.glueData.ι U ≫ I.gluedTo).base x ∈ X.basicOpen r ∧
      letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
        GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
      Algebra.IsStandardSmoothOfRelativeDimension 1 R
        (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r)) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI := quotient_chart_smooth f I U
  obtain ⟨t, htx, ht⟩ := SchemeSmoothPrincipalLocalization.exists_away 1
    (algebraMap R (Γ(X, U.1) ⧸ I.ideal U)) x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨r, (chart_point_basicOpen_iff I U r x).mpr htx, ?_⟩
  letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  letI := restrictionAlgebra U r
  letI := restrictionTower f U r
  letI := quotientAlgebra I U r
  letI := KltDP.RingTheory.SmoothPrincipalDeterminantRestriction.quotientMapTowerR R
    Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) (I.ideal U) (I.ideal (X.affineBasicOpen r))
    (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))
  letI := quotient_isLocalization I U r
  have hs := ht (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))
  rw [← IsScalarTower.algebraMap_eq R (Γ(X, U.1) ⧸ I.ideal U)
    (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))] at hs
  exact SchemeSmoothPrincipalLocalization.standardSmooth_of_algebraMap 1 hs

end KltDP.Geometry.GluedAdjunctionQuotientSmoothNeighborhood
