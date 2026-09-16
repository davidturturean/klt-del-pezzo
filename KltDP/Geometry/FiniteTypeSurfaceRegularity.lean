import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.Geometry.SurfaceRegularCharts
import KltDP.Geometry.ClosedPoints
import KltDP.Literature.Definitions.J2
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Regularity and singular finiteness for arbitrary normal finite-type surfaces

The scheme is arbitrary: it need not be projective, integral, nonempty,
connected, or of dimension exactly two. Its stated geometric inputs are
normality of the actual stalks, topological dimension at most two, and a
finite-type structure morphism to the spectrum of a field.

At this Mathlib pin, a finite-type morphism is expressed by the two actual
classes `LocallyOfFiniteType` and `QuasiCompact`. Local finite type suffices
for the conditional regular-locus openness theorem. Quasi-compactness is
used for the global Noetherian topology and finite singular set.

The only literature condition is the literal `Literature.J2Ring k`, kept
as an explicit proposition argument. The affine algebras, localization
domains, dimension bounds, generator/cotangent comparison, pointwise
closedness, and final finiteness are independently derived. No field-J2
axiom is declared or used by this module.

See `docs/FINITE_TYPE_SURFACE_REGULARITY_SCOPE.md` for the complete
hypothesis comparison and source-only verification status.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- A finite-type scheme over an actual Noetherian affine base is
Noetherian. The pin expresses finite type as local finite type plus
quasi-compactness; no domain or irreducibility assumption is needed. -/
theorem isNoetherian_of_finiteType_toSpec
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian X := by
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_locallyOfFiniteType_toSpec f
  letI : CompactSpace X := (quasiCompact_over_affine_iff f).mp inferInstance
  exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

/-- Normality makes the actual prime localizations on any affine chart
domains, and ambient dimension at most two bounds their local dimension.
The previously proved generator/cotangent equivalence therefore applies
without requiring the whole scheme or its chart ring to be a domain. -/
theorem affineLocalization_regular_iff_generators_of_normal_of_dimension_le_two
    {X : Scheme.{u}} (hnormal : IsNormalScheme X)
    (hdim : topologicalKrullDim X ≤ 2) {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] (p : PrimeSpectrum R) :
    RegularLocal (Localization.AtPrime p.asIdeal) ↔
      RegularLocalByGenerators (Localization.AtPrime p.asIdeal) := by
  letI : IsDomain (X.presheaf.stalk (j.base p)) := (hnormal (j.base p)).1
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

/-- The actual regular prime locus on a chart is exactly the literal
generator locus appearing in J-1 and J-2. This equality is proved pointwise
from normal stalks and the ambient dimension bound. -/
theorem primeLocalizationRegularLocus_eq_generatorRegularLocus_of_normal_of_dimension_le_two
    {X : Scheme.{u}} (hnormal : IsNormalScheme X)
    (hdim : topologicalKrullDim X ≤ 2) {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] :
    primeLocalizationRegularLocus R = Literature.generatorRegularLocus R := by
  ext p
  exact affineLocalization_regular_iff_generators_of_normal_of_dimension_le_two
    hnormal hdim j p

/-- Conditional openness for every normal scheme locally of finite type
over a J-2 field in dimension at most two. No projectivity, integrality,
or global quasi-compactness is required for this local conclusion. -/
theorem normalLocallyFiniteType_regularLocus_isOpen_of_J2
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (hk : Literature.J2Ring.{u, u} k) : IsOpen (regularLocus X) := by
  apply isOpen_regularLocus_of_primeLocalizationOpen_on_affineCover X.affineOpenCover
  intro i
  letI : Algebra k (X.affineOpenCover.obj i) :=
    (Spec.preimage (X.affineOpenCover.map i ≫ f)).hom.toAlgebra
  letI : Algebra.FiniteType k (X.affineOpenCover.obj i) := by
    have hcomp : LocallyOfFiniteType (X.affineOpenCover.map i ≫ f) := inferInstance
    rw [← Spec.map_preimage (X.affineOpenCover.map i ≫ f)] at hcomp
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hcomp
  have hlocus : primeLocalizationRegularLocus (X.affineOpenCover.obj i) =
      Literature.generatorRegularLocus (X.affineOpenCover.obj i) :=
    primeLocalizationRegularLocus_eq_generatorRegularLocus_of_normal_of_dimension_le_two
      (R := X.affineOpenCover.obj i) hnormal hdim (X.affineOpenCover.map i)
  rw [hlocus]
  exact hk.isOpen_generatorRegularLocus (X.affineOpenCover.obj i)

/-- Pointwise closedness of singular points uses normality, local finite
type, and dimension at most two. It needs no J-2 input or projectivity. -/
theorem normalLocallyFiniteType_singularPoint_isClosed
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) (hx : x ∈ singularLocus X) : IsClosed ({x} : Set X) := by
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_locallyOfFiniteType_toSpec f
  letI : IsNoetherianRing (X.presheaf.stalk x) :=
    isNoetherianRing_stalk_of_isLocallyNoetherian X x
  exact singularPoint_isClosed_of_dimension_le_two X hnormal hdim x hx

/-- The singular locus is closed once the literal field-J2 condition
provides regular-locus openness. -/
theorem normalLocallyFiniteType_singularLocus_isClosed_of_J2
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (hk : Literature.J2Ring.{u, u} k) : IsClosed (singularLocus X) :=
  (isClosed_singularLocus_iff_isOpen_regularLocus X).mpr
    (normalLocallyFiniteType_regularLocus_isOpen_of_J2 f hnormal hdim hk)

/-- Every actual normal finite-type scheme over a J-2 field of
topological dimension at most two has only finitely many singular points.
The complete finite-type hypothesis is the pinned pair of morphism classes. -/
theorem normalFiniteType_singularLocus_finite_of_J2
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (hk : Literature.J2Ring.{u, u} k) : (singularLocus X).Finite := by
  letI : IsNoetherian X := isNoetherian_of_finiteType_toSpec f
  exact singularLocus_finite_of_isClosed_of_closedPoints X
    (normalLocallyFiniteType_singularLocus_isClosed_of_J2 f hnormal hdim hk)
    (fun x hx => normalLocallyFiniteType_singularPoint_isClosed f hnormal hdim x hx)

/-- The actual finite singular set, with exact nonregular-stalk
membership, is constructed only after the general finiteness proof. -/
theorem normalFiniteType_exists_singularPointFinset_of_J2
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (hk : Literature.J2Ring.{u, u} k) :
    ∃ s : Finset X, ∀ x : X, x ∈ s ↔ ¬ RegularLocal (X.presheaf.stalk x) :=
  ⟨singularPointFinset X (normalFiniteType_singularLocus_finite_of_J2 f hnormal hdim hk),
    mem_singularPointFinset X (normalFiniteType_singularLocus_finite_of_J2 f hnormal hdim hk)⟩

/-- At every actual singular point, the canonical base-to-residue-field
map is finite. Closedness is proved above; neither J-2 nor global singular
finiteness is needed for this residue-field conclusion. -/
theorem normalLocallyFiniteType_singularResidueField_finite
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) (hx : x ∈ singularLocus X) :
    (baseToResidueFieldMap f x).hom.Finite :=
  baseToResidueFieldMap_finite f x
    (normalLocallyFiniteType_singularPoint_isClosed f hnormal hdim x hx)

/-- Over an algebraically closed base, the same actual residue-field map
is bijective. This is an unconditional pointwise consequence of normality
and the dimension bound, independent of the J-2 openness input. -/
theorem normalLocallyFiniteType_singularResidueField_bijective
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) (hx : x ∈ singularLocus X) :
    Function.Bijective (baseToResidueFieldMap f x).hom :=
  baseToResidueFieldMap_bijective f x
    (normalLocallyFiniteType_singularPoint_isClosed f hnormal hdim x hx)

/-- Over an algebraically closed base, every actual singular point is
represented by an actual section `Spec k → X` of the given structure map,
with the prescribed underlying point. -/
theorem normalLocallyFiniteType_singularPoint_has_section
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (x : X) (hx : x ∈ singularLocus X) :
    ∃ g : Spec (CommRingCat.of k) ⟶ X,
      g ≫ f = 𝟙 (Spec (CommRingCat.of k)) ∧
        ∀ t : Spec (CommRingCat.of k), g.base t = x := by
  have hclosed := normalLocallyFiniteType_singularPoint_isClosed f hnormal hdim x hx
  exact ⟨closedPointSection f x hclosed, closedPointSection_over_base f x hclosed,
    closedPointSection_base f x hclosed⟩

/-- The general finite singular set has the existing singular count as
its cardinality. Both the enumeration and the count use the actual
singular locus and the preceding finiteness proof. -/
theorem normalFiniteType_exists_singularPointFinset_with_card_of_J2
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hnormal : IsNormalScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (hk : Literature.J2Ring.{u, u} k) :
    ∃ s : Finset X,
      (∀ x : X, x ∈ s ↔ ¬ RegularLocal (X.presheaf.stalk x)) ∧
        nSing X (normalFiniteType_singularLocus_finite_of_J2 f hnormal hdim hk) = s.card :=
  ⟨singularPointFinset X (normalFiniteType_singularLocus_finite_of_J2 f hnormal hdim hk),
    mem_singularPointFinset X (normalFiniteType_singularLocus_finite_of_J2 f hnormal hdim hk),
    rfl⟩

end KltDP.Geometry
