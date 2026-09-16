import KltDP.Geometry.RegularLocusLocal
import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Regularity on spectra and prime localizations

The actual structure-sheaf stalk at a point `p` of `Spec R` is isomorphic
to `Localization.AtPrime p.asIdeal`. Transporting the regular-local
predicate across this isomorphism identifies the scheme's regular locus
with the set of primes whose actual localizations are regular.

Openness then transfers across this exact set identification and along
actual affine open covers. Every local openness assertion is an explicit
hypothesis; this module supplies no general regular-locus openness theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.Geometry

/-- The regular primes, defined using the original ring's actual prime
localizations and their actual maximal-ideal cotangent spaces. -/
def primeLocalizationRegularLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  {p | RegularLocal (Localization.AtPrime p.asIdeal)}

/-- The structure sheaf's actual stalk-localization isomorphism, as a
ring equivalence between the two existing rings. -/
def specStalkLocalizationEquiv (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    (Spec (CommRingCat.of R)).presheaf.stalk p ≃+* Localization.AtPrime p.asIdeal :=
  (StructureSheaf.stalkIso R p).commRingCatIsoToRingEquiv

/-- Scheme-theoretic regularity at `p` is exactly regularity of `Rₚ`. -/
theorem regularPoint_spec_iff (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    RegularPoint (Spec (CommRingCat.of R)) p ↔
      RegularLocal (Localization.AtPrime p.asIdeal) :=
  regularLocal_iff_of_ringEquiv (specStalkLocalizationEquiv R p)

/-- The two regular loci are equal as subsets of the same prime spectrum,
with its original Zariski topology. -/
theorem regularLocus_spec_eq_primeLocalizationRegularLocus
    (R : Type u) [CommRing R] :
    regularLocus (Spec (CommRingCat.of R)) = primeLocalizationRegularLocus R := by
  ext p
  exact regularPoint_spec_iff R p

/-- An explicit openness proof about prime localizations is equivalent to
openness of the actual affine scheme's regular locus. -/
theorem isOpen_regularLocus_spec_iff (R : Type u) [CommRing R] :
    IsOpen (regularLocus (Spec (CommRingCat.of R))) ↔
      IsOpen (primeLocalizationRegularLocus R) := by
  rw [regularLocus_spec_eq_primeLocalizationRegularLocus]

/-- At a point supplied by an actual affine-open immersion, regularity is
equivalent to regularity of the corresponding localization of its sections. -/
theorem regularPoint_fromSpec_iff {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (p : PrimeSpectrum Γ(X, U)) :
    RegularPoint X (hU.fromSpec.base p) ↔
      RegularLocal (Localization.AtPrime p.asIdeal) :=
  (regularPoint_iff_of_isOpenImmersion hU.fromSpec p).symm.trans
    (regularPoint_spec_iff Γ(X, U) p)

/-- The same comparison at an existing point of an affine open uses the
prime ideal provided by the actual affine-open equivalence. -/
theorem regularPoint_iff_regularLocal_affineLocalization
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : U) :
    RegularPoint X x.1 ↔
      RegularLocal (Localization.AtPrime (hU.primeIdealOf x).asIdeal) := by
  simpa only [hU.fromSpec_primeIdealOf x] using
    regularPoint_fromSpec_iff hU (hU.primeIdealOf x)

/-- The exact inverse image of the scheme's regular locus on an affine chart. -/
theorem regularLocus_preimage_fromSpec {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) :
    hU.fromSpec.base ⁻¹' regularLocus X = primeLocalizationRegularLocus Γ(X, U) := by
  rw [← regularLocus_preimage_of_isOpenImmersion hU.fromSpec,
    regularLocus_spec_eq_primeLocalizationRegularLocus]

/-- The regular points lying in an affine open are precisely the image of
its regular prime localizations under the actual chart immersion. -/
theorem regularLocus_inter_affineOpen_eq_image {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) :
    regularLocus X ∩ (U : Set X) =
      hU.fromSpec.base '' primeLocalizationRegularLocus Γ(X, U) := by
  rw [← regularLocus_preimage_fromSpec hU, Set.image_preimage_eq_inter_range,
    hU.range_fromSpec]

/-- Local openness of the prime-localization predicate makes the regular
part of the given affine open an open subset of the original scheme. -/
theorem isOpen_regularLocus_inter_affineOpen_of_primeLocalizationOpen
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (hopen : IsOpen (primeLocalizationRegularLocus Γ(X, U))) :
    IsOpen (regularLocus X ∩ (U : Set X)) := by
  rw [regularLocus_inter_affineOpen_eq_image hU]
  exact hU.fromSpec.isOpenEmbedding.isOpenMap _ hopen

/-- On an actual affine open cover, the required local openness assertions
can be stated entirely in terms of its coordinate-ring localizations. -/
theorem isOpen_regularLocus_iff_primeLocalizationOpen_on_affineCover
    {X : Scheme.{u}} (𝒰 : Scheme.AffineOpenCover.{v, u} X) :
    IsOpen (regularLocus X) ↔
      ∀ i, IsOpen (primeLocalizationRegularLocus (𝒰.obj i)) := by
  rw [isOpen_regularLocus_iff_of_affineOpenCover 𝒰]
  exact forall_congr' fun i ↦ isOpen_regularLocus_spec_iff (𝒰.obj i)

/-- This local-to-global conclusion retains an explicit openness proof for
the prime-localization locus on every affine member of the given cover. -/
theorem isOpen_regularLocus_of_primeLocalizationOpen_on_affineCover
    {X : Scheme.{u}} (𝒰 : Scheme.AffineOpenCover.{v, u} X)
    (hopen : ∀ i, IsOpen (primeLocalizationRegularLocus (𝒰.obj i))) :
    IsOpen (regularLocus X) :=
  (isOpen_regularLocus_iff_primeLocalizationOpen_on_affineCover 𝒰).mpr hopen

end KltDP.Geometry
