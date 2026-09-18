import KltDP.Geometry.AffineFiniteType
import KltDP.Geometry.SurfaceRegularCharts
import KltDP.Geometry.DivisorOrder
import KltDP.Literature.Stacks.FieldJ2

/-!
# Regular-locus openness on integral finite-type schemes of dimension at most two

The actual affine localizations are domains because the original scheme
is integral. Their dimensions are bounded by the original scheme dimension,
so the proved generator/cotangent comparison applies without normality.
The already admitted literal field-J2 theorem then gives openness for the
actual chart algebras, whose base maps are the original composites.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Integral-scheme stalks supply the domain hypothesis in the actual
affine-localization generator/cotangent comparison. -/
theorem affineLocalization_regular_iff_generators_of_integral_of_dimension_le_two
    {X : Scheme.{u}} [IsIntegral X] (hdim : topologicalKrullDim X ≤ 2)
    {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] (p : PrimeSpectrum R) :
    RegularLocal (Localization.AtPrime p.asIdeal) ↔
      RegularLocalByGenerators (Localization.AtPrime p.asIdeal) := by
  letI : IsDomain (X.presheaf.stalk (j.base p)) :=
    integralSchemeStalk_isDomain X (j.base p)
  letI : IsDomain (Localization.AtPrime p.asIdeal) :=
    MulEquiv.isDomain (X.presheaf.stalk (j.base p))
      (openImmersionStalkLocalizationEquiv j p).symm.toMulEquiv
  have hlocal : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ 2 := by
    calc
      ringKrullDim (Localization.AtPrime p.asIdeal) =
          ringKrullDim (X.presheaf.stalk (j.base p)) :=
        (ringKrullDim_eq_of_ringEquiv (openImmersionStalkLocalizationEquiv j p)).symm
      _ ≤ 2 := (ringKrullDim_stalk_le_topologicalKrullDim X (j.base p)).trans hdim
  exact (regularLocalByGenerators_iff_regularLocal_of_dimension_le_two hlocal).symm

/-- The actual regular locus is open for an integral scheme locally of
finite type over a field and of dimension at most two. No normality,
projectivity, smoothness, or algebraic-closure hypothesis is used. -/
theorem integralLocallyFiniteType_regularLocus_isOpen
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 2) : IsOpen (regularLocus X) := by
  apply isOpen_regularLocus_of_primeLocalizationOpen_on_affineCover X.affineOpenCover
  intro i
  letI : Algebra k (X.affineOpenCover.obj i) :=
    (Spec.preimage (X.affineOpenCover.map i ≫ f)).hom.toAlgebra
  letI : Algebra.FiniteType k (X.affineOpenCover.obj i) := by
    have hcomp : LocallyOfFiniteType (X.affineOpenCover.map i ≫ f) := inferInstance
    rw [← Spec.map_preimage (X.affineOpenCover.map i ≫ f)] at hcomp
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hcomp
  have hlocus : primeLocalizationRegularLocus (X.affineOpenCover.obj i) =
      Literature.generatorRegularLocus (X.affineOpenCover.obj i) := by
    ext p
    exact affineLocalization_regular_iff_generators_of_integral_of_dimension_le_two
      hdim (X.affineOpenCover.map i) p
  rw [hlocus]
  exact (Literature.Stacks.field_isJ2.{u, u} k).isOpen_generatorRegularLocus
    (X.affineOpenCover.obj i)

end KltDP.Geometry
