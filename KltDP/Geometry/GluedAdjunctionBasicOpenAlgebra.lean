import KltDP.Geometry.GluedChartKaehlerPullback
import KltDP.Geometry.GluedConormalBasicOpenLocalization
import KltDP.RingTheory.SmoothPrincipalDeterminantLocalization

/-!
# The actual base algebras and smoothness on basic-open adjunction charts

The restriction algebra is the original section map. Compatibility with the
original global base morphism supplies its scalar tower. The pinned principal
localization theorems preserve the ambient and quotient relative dimensions,
so the smaller adjunction chart needs no additional smoothness assumptions.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra

open GluedConormalBasicOpenLocalization

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
  (U : X.affineOpens) (r : Γ(X, U.1))

/-- The algebra on the smaller section ring is induced by the original restriction. -/
abbrev restrictionAlgebra : Algebra Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
  (sectionMap U r).toAlgebra

/-- The original restriction commutes with the original global base algebra. -/
theorem restrictionTower :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
      GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
    letI := restrictionAlgebra U r
    IsScalarTower R Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  letI := restrictionAlgebra U r
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (congrArg (fun g : CommRingCat.of R ⟶ Γ(X, (X.affineBasicOpen r).1) => g.hom a)
    (baseToAffineSectionsMap_restrict f U.2 (X.affineBasicOpen r).2
      (X.affineBasicOpen_le r))).symm

/-- Original ambient standard smoothness of dimension two survives the actual basic open. -/
theorem ambient_standardSmooth :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
      GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)],
      Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, (X.affineBasicOpen r).1) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  intro _
  letI := restrictionAlgebra U r
  letI := restrictionTower f U r
  letI : IsLocalization.Away r Γ(X, (X.affineBasicOpen r).1) := U.2.isLocalization_basicOpen r
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0
      Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away r
  simpa only [Nat.zero_add] using
    (Algebra.IsStandardSmoothOfRelativeDimension.trans R Γ(X, U.1)
      Γ(X, (X.affineBasicOpen r).1) (n := 2) (m := 0))

/-- The original quotient algebra is induced by the original chart quotient map. -/
abbrev quotientAlgebra : Algebra (Γ(X, U.1) ⧸ I.ideal U)
    (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r)) :=
  (quotientMap I U r).toAlgebra

/-- The actual quotient chart is the principal localization of the original quotient ring. -/
theorem quotient_isLocalization :
    letI := quotientAlgebra I U r
    IsLocalization.Away (Ideal.Quotient.mk (I.ideal U) r)
      (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r)) := by
  letI := restrictionAlgebra U r
  letI := quotientAlgebra I U r
  letI : IsLocalization.Away r Γ(X, (X.affineBasicOpen r).1) := U.2.isLocalization_basicOpen r
  simp only [IsLocalization.Away, ← Submonoid.map_powers]
  refine IsLocalization.of_surjective (Submonoid.powers r) Γ(X, (X.affineBasicOpen r).1)
    (Ideal.Quotient.mk (I.ideal U)) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (I.ideal (X.affineBasicOpen r))) Ideal.Quotient.mk_surjective ?_ ?_
  · apply RingHom.ext
    intro a
    exact (Ideal.quotientMap_mk (J := I.ideal U) (I := I.ideal (X.affineBasicOpen r))
      (f := sectionMap U r) (H := I.ideal_le_comap_ideal (X.affineBasicOpen_le r))
      (x := a)).symm
  · simp only [Ideal.mk_ker]
    exact (I.map_ideal (X.affineBasicOpen_le r)).ge

/-- Original quotient standard smoothness of dimension one survives the actual basic open. -/
theorem quotient_standardSmooth :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
      GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      Algebra.IsStandardSmoothOfRelativeDimension 1 R
        (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r)) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  intro _
  letI := restrictionAlgebra U r
  letI := restrictionTower f U r
  letI := quotientAlgebra I U r
  letI := KltDP.RingTheory.SmoothPrincipalDeterminantRestriction.quotientMapTowerR R
    Γ(X, U.1) Γ(X, (X.affineBasicOpen r).1) (I.ideal U) (I.ideal (X.affineBasicOpen r))
    (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))
  letI := quotient_isLocalization I U r
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 (Γ(X, U.1) ⧸ I.ideal U)
      (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (Ideal.Quotient.mk (I.ideal U) r)
  simpa only [Nat.zero_add] using
    (Algebra.IsStandardSmoothOfRelativeDimension.trans R (Γ(X, U.1) ⧸ I.ideal U)
      (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r)) (n := 1) (m := 0))

end KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra
