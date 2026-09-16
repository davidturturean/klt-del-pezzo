import KltDP.Geometry.AffineFiniteType
import KltDP.Geometry.AffineRegularLocus
import KltDP.Geometry.RegularLocalDimensionTwo

/-!
# Generator regularity on actual normal-surface affine charts

An affine chart's prime localization is isomorphic to the actual surface
stalk at the image point. Thus it is a Noetherian domain of dimension at
most two. The proved dimension-two comparison identifies cotangent
regularity with the literal maximal-ideal generator definition there.

The finite-type algebra on a chart comes from its actual composite to the
base field. The generator-regular prime loci recover the surface's regular
locus on charts and covers. Any openness conclusion still requires explicit
openness of those generator-regular prime loci.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.Geometry

/-- The literal generator-regular primes of a ring, formed using its actual
prime localizations. -/
def primeLocalizationGeneratorRegularLocus (R : Type u) [CommRing R] :
    Set (PrimeSpectrum R) :=
  {p | RegularLocalByGenerators (Localization.AtPrime p.asIdeal)}

/-- The actual stalk equivalence attached to an affine open immersion,
followed by the structure sheaf's stalk-localization equivalence. -/
def openImmersionStalkLocalizationEquiv {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j] (p : PrimeSpectrum R) :
    Y.presheaf.stalk (j.base p) ≃+* Localization.AtPrime p.asIdeal :=
  ((asIso (j.stalkMap p)).commRingCatIsoToRingEquiv).trans
    (specStalkLocalizationEquiv R p)

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The base algebra on any actual affine chart is induced by its composite
with the original surface structure morphism. -/
abbrev affineChartAlgebra {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) : Algebra k R :=
  (Spec.preimage (j ≫ X.structureMorphism)).hom.toAlgebra

@[simp]
theorem affineChartAlgebra_algebraMap {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) :
    letI := X.affineChartAlgebra j
    algebraMap k R = (Spec.preimage (j ≫ X.structureMorphism)).hom := rfl

/-- Finite type is proved for the same chart-to-base homomorphism. -/
theorem affineChartAlgebra_finiteType {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j] :
    letI := X.affineChartAlgebra j
    Algebra.FiniteType k R := by
  have hcomp : LocallyOfFiniteType (j ≫ X.structureMorphism) := inferInstance
  rw [← Spec.map_preimage (j ≫ X.structureMorphism)] at hcomp
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hcomp

/-- Every localization at a prime of an actual affine chart is a domain,
by its isomorphism with the integral surface's actual stalk. -/
theorem affineLocalization_isDomain {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (p : PrimeSpectrum R) : IsDomain (Localization.AtPrime p.asIdeal) :=
  MulEquiv.isDomain (X.stalk (j.base p))
    (openImmersionStalkLocalizationEquiv j p).symm.toMulEquiv

/-- The same localization is Noetherian by transport from the actual
Noetherian surface stalk. -/
theorem affineLocalization_isNoetherianRing {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (p : PrimeSpectrum R) : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
  isNoetherianRing_of_ringEquiv (X.stalk (j.base p))
    (openImmersionStalkLocalizationEquiv j p)

/-- Its Krull dimension is bounded by the actual surface dimension. -/
theorem affineLocalization_ringKrullDim_le_two {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (p : PrimeSpectrum R) : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ 2 := by
  calc
    ringKrullDim (Localization.AtPrime p.asIdeal) =
        ringKrullDim (X.stalk (j.base p)) :=
      (ringKrullDim_eq_of_ringEquiv (openImmersionStalkLocalizationEquiv j p)).symm
    _ ≤ 2 := (ringKrullDim_stalk_le_topologicalKrullDim X.toScheme (j.base p)).trans_eq
      X.dimension_two

/-- The two regular-local predicates agree at every prime localization of
an actual affine chart, with their dimension hypotheses proved above. -/
theorem affineLocalization_regular_iff_generators {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (p : PrimeSpectrum R) :
    RegularLocal (Localization.AtPrime p.asIdeal) ↔
      RegularLocalByGenerators (Localization.AtPrime p.asIdeal) := by
  letI : IsDomain (Localization.AtPrime p.asIdeal) := X.affineLocalization_isDomain j p
  exact (regularLocalByGenerators_iff_regularLocal_of_dimension_le_two
    (X.affineLocalization_ringKrullDim_le_two j p)).symm

/-- Scheme regularity at a chart image is the literal generator regularity
of the corresponding coordinate-ring localization. -/
theorem regularPoint_affineChart_iff_generators {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (p : PrimeSpectrum R) :
    RegularPoint X.toScheme (j.base p) ↔
      RegularLocalByGenerators (Localization.AtPrime p.asIdeal) :=
  ((regularPoint_iff_of_isOpenImmersion j p).symm.trans (regularPoint_spec_iff R p)).trans
    (X.affineLocalization_regular_iff_generators j p)

/-- The exact equality of the two prime loci on an actual chart. -/
theorem primeLocalizationRegularLocus_eq_generatorRegularLocus
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ X.toScheme)
    [IsOpenImmersion j] :
    primeLocalizationRegularLocus R = primeLocalizationGeneratorRegularLocus R := by
  ext p
  exact X.affineLocalization_regular_iff_generators j p

/-- The preimage of the surface's regular locus on the actual chart is
exactly the literal generator-regular prime locus. -/
theorem regularLocus_preimage_affineChart_eq_generatorRegularLocus
    {R : Type u} [CommRing R] (j : Spec (CommRingCat.of R) ⟶ X.toScheme)
    [IsOpenImmersion j] :
    j.base ⁻¹' regularLocus X.toScheme = primeLocalizationGeneratorRegularLocus R := by
  ext p
  exact X.regularPoint_affineChart_iff_generators j p

/-- An actual affine cover recovers the surface's regular locus from the
images of its literal generator-regular prime loci. -/
theorem regularLocus_eq_iUnion_image_generatorRegularLocus
    (𝒰 : Scheme.AffineOpenCover.{v, u} X.toScheme) :
    regularLocus X.toScheme =
      ⋃ i, (𝒰.map i).base '' primeLocalizationGeneratorRegularLocus (𝒰.obj i) := by
  rw [regularLocus_eq_iUnion_image_of_openCover 𝒰.openCover]
  apply Set.iUnion_congr
  intro i
  change (𝒰.map i).base '' regularLocus (Spec (𝒰.obj i)) =
    (𝒰.map i).base '' primeLocalizationGeneratorRegularLocus (𝒰.obj i)
  rw [regularLocus_spec_eq_primeLocalizationRegularLocus,
    X.primeLocalizationRegularLocus_eq_generatorRegularLocus (𝒰.map i)]

/-- The literal source openness hypotheses on the coordinate rings are
equivalent to regular-locus openness on the given surface. -/
theorem isOpen_regularLocus_iff_generatorRegularLocus_on_affineCover
    (𝒰 : Scheme.AffineOpenCover.{v, u} X.toScheme) :
    IsOpen (regularLocus X.toScheme) ↔
      ∀ i, IsOpen (primeLocalizationGeneratorRegularLocus (𝒰.obj i)) := by
  rw [isOpen_regularLocus_iff_primeLocalizationOpen_on_affineCover 𝒰]
  apply forall_congr'
  intro i
  rw [X.primeLocalizationRegularLocus_eq_generatorRegularLocus (𝒰.map i)]

/-- This implication requires the explicit generator-locus openness proofs;
the surface hypotheses alone are not used to assert them. -/
theorem isOpen_regularLocus_of_generatorRegularLocus_on_affineCover
    (𝒰 : Scheme.AffineOpenCover.{v, u} X.toScheme)
    (hopen : ∀ i, IsOpen (primeLocalizationGeneratorRegularLocus (𝒰.obj i))) :
    IsOpen (regularLocus X.toScheme) :=
  (X.isOpen_regularLocus_iff_generatorRegularLocus_on_affineCover 𝒰).mpr hopen

end NormalProjectiveSurface

end KltDP.Geometry
