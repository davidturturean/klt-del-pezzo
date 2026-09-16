import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.GradedAlgebra.Noetherian
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.KrullDimension

/-!
# Actual normal projective surfaces

The pinned mathlib version has schemes and `Proj`, but does not provide a general
projective-morphism predicate. Here projectivity over a field has its usual
definition: a closed immersion into a finite-dimensional projective space,
compatible with the structure morphism. No geometric consequences are fields of
the surface structure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Forget homogeneity and relevance, retaining the actual prime ideal. -/
def projectiveSpectrumToPrimeSpectrum {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (x : ProjectiveSpectrum 𝒜) : PrimeSpectrum A :=
  ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

/-- The topology on the projective spectrum is induced by its inclusion in
the prime spectrum of the graded ring. Both closed-set definitions are zero
loci of subsets of the same ring. -/
theorem projectiveSpectrumToPrimeSpectrum_isInducing {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    Topology.IsInducing (projectiveSpectrumToPrimeSpectrum 𝒜) := by
  refine ⟨TopologicalSpace.ext_isClosed fun Z ↦ ?_⟩
  rw [ProjectiveSpectrum.isClosed_iff_zeroLocus, isClosed_induced_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨PrimeSpectrum.zeroLocus s, PrimeSpectrum.isClosed_zeroLocus s, rfl⟩
  · rintro ⟨s, hs, hpreimage⟩
    obtain ⟨a, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus s).mp hs
    exact ⟨a, hpreimage.symm⟩

/-- Noetherianity of the graded ring implies Noetherianity of the underlying
projective spectrum, by its induced topology inside the affine spectrum. -/
theorem projectiveSpectrum_noetherianSpace {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    NoetherianSpace (ProjectiveSpectrum 𝒜) :=
  (projectiveSpectrumToPrimeSpectrum_isInducing 𝒜).noetherianSpace

/-- The usual homogeneous affine cover proves local Noetherianity of a
finitely generated graded algebra over its degree-zero ring. -/
theorem proj_isLocallyNoetherian {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [IsNoetherianRing A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    [Algebra.FiniteType (𝒜 0) A] : IsLocallyNoetherian (Proj 𝒜) := by
  apply (isLocallyNoetherian_iff_openCover (Proj.affineOpenCover 𝒜).openCover).mpr
  intro i
  letI : Algebra.FiniteType (𝒜 0) (HomogeneousLocalization.Away 𝒜 i.2) :=
    HomogeneousLocalization.Away.finiteType (𝒜 := 𝒜) (i.2 : A) (i.1 : ℕ) i.2.2
  letI : IsNoetherianRing (HomogeneousLocalization.Away 𝒜 i.2) :=
    Algebra.FiniteType.isNoetherianRing (𝒜 0) _
  change IsLocallyNoetherian (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 i.2)))
  infer_instance

/-- Stalks of a locally Noetherian scheme are Noetherian, using the canonical
localization of an affine neighborhood at the point's prime ideal. -/
theorem isNoetherianRing_stalk_of_isLocallyNoetherian
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  let U : X.Opens := (X.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map x)
  let xu : U := ⟨x, X.affineCover.covers x⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk xu
  letI : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf xu).asIdeal := hU.isLocalization_stalk xu
  exact IsLocalization.isNoetherianRing (hU.primeIdealOf xu).asIdeal.primeCompl
    (X.presheaf.stalk x) (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective `n`-space, as the scheme `Proj k[x₀, …, xₙ]`. -/
def projectiveSpace (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)

/-- Finite-dimensional projective space has Noetherian underlying topology. -/
theorem projectiveSpace_noetherianSpace (k : Type u) [Field k] (n : ℕ) :
    NoetherianSpace (projectiveSpace k n) :=
  projectiveSpectrum_noetherianSpace
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)

/-- Local Noetherianity of actual projective space follows from its polynomial
homogeneous coordinate ring and its standard homogeneous affine cover. -/
theorem projectiveSpace_isLocallyNoetherian (k : Type u) [Field k] (n : ℕ) :
    IsLocallyNoetherian (projectiveSpace k n) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k
  letI : Algebra.FiniteType k (MvPolynomial (Fin (n + 1)) k) :=
    Algebra.FiniteType.mvPolynomial k (Fin (n + 1))
  letI : IsScalarTower k (𝒜 0) (MvPolynomial (Fin (n + 1)) k) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := 𝒜 0)
      (A := MvPolynomial (Fin (n + 1)) k) (fun _ ↦ rfl)
  letI : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (n + 1)) k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (𝒜 0) _
  exact proj_isLocallyNoetherian 𝒜

/-- Constants as degree-zero homogeneous polynomials. -/
def projectiveSpaceConstants (k : Type u) [Field k] (n : ℕ) :
    k →+* MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C _ a⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)

/-- The canonical structure morphism from projective space to the base field. -/
def projectiveSpaceToSpec (k : Type u) [Field k] (n : ℕ) :
    projectiveSpace k n ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ≫
    Spec.map (CommRingCat.ofHom (projectiveSpaceConstants k n))

/-- Projectivity over a field, defined by a genuine closed projective embedding. -/
def IsProjectiveOverField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ projectiveSpace k n),
    IsClosedImmersion i ∧ i ≫ projectiveSpaceToSpec k n = f

/-- Noetherian topology follows from the actual projective embedding; it is
not an extra field in the projective-surface wrapper. -/
theorem IsProjectiveOverField.noetherianSpace {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (hf : IsProjectiveOverField f) : NoetherianSpace X := by
  obtain ⟨n, i, hi, _⟩ := hf
  letI : IsClosedImmersion i := hi
  letI : NoetherianSpace (projectiveSpace k n) := projectiveSpace_noetherianSpace k n
  exact i.isClosedEmbedding.isInducing.noetherianSpace

/-- A projective embedding makes every source stalk a quotient of a
Noetherian projective-space stalk. -/
theorem IsProjectiveOverField.isNoetherianRing_stalk {k : Type u} [Field k]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (hf : IsProjectiveOverField f) (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨n, i, hi, _⟩ := hf
  letI : IsClosedImmersion i := hi
  letI : IsLocallyNoetherian (projectiveSpace k n) :=
    projectiveSpace_isLocallyNoetherian k n
  letI : IsNoetherianRing ((projectiveSpace k n).presheaf.stalk (i.base x)) :=
    isNoetherianRing_stalk_of_isLocallyNoetherian _ _
  exact isNoetherianRing_of_surjective _ _ (i.stalkMap x).hom (i.stalkMap_surjective x)

/-- A scheme is normal when every local ring is an integrally closed domain.
The domain requirement is explicit because mathlib's `IsIntegrallyClosed`
alone also makes sense for rings with zero divisors. -/
def IsNormalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- An integral normal projective scheme of Krull dimension two over `k`.
The fields are precisely the stated defining geometric hypotheses. -/
structure NormalProjectiveSurface (k : Type u) [Field k] where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ Spec (CommRingCat.of k)
  integral : IsIntegral toScheme
  normal : IsNormalScheme toScheme
  projective : IsProjectiveOverField structureMorphism
  dimension_two : topologicalKrullDim toScheme = 2

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

instance : IsIntegral X.toScheme := X.integral

instance : NoetherianSpace X.toScheme := X.projective.noetherianSpace

/-- Actual topological scheme points; these include generic points. -/
abbrev Point := X.toScheme

/-- The actual structure-sheaf stalk at a point. -/
abbrev stalk (x : X.Point) : CommRingCat := X.toScheme.presheaf.stalk x

instance (x : X.Point) : IsNoetherianRing (X.stalk x) :=
  X.projective.isNoetherianRing_stalk x

instance (x : X.Point) : IsDomain (X.stalk x) := (X.normal x).1

instance (x : X.Point) : IsIntegrallyClosed (X.stalk x) := (X.normal x).2

/-- A `k`-rational point is a section of the structure morphism. It is distinct
from an arbitrary underlying scheme point, which need not be closed. -/
structure RationalPoint where
  morphism : Spec (CommRingCat.of k) ⟶ X.toScheme
  over_base : morphism ≫ X.structureMorphism = 𝟙 (Spec (CommRingCat.of k))

/-- The embedding in the definition of projectivity is injective on points. -/
theorem exists_projective_embedding :
    ∃ (n : ℕ) (i : X.toScheme ⟶ projectiveSpace k n),
      IsClosedImmersion i ∧ Function.Injective i.base ∧
        i ≫ projectiveSpaceToSpec k n = X.structureMorphism := by
  obtain ⟨n, i, hi, hfactor⟩ := X.projective
  letI := hi
  exact ⟨n, i, hi, i.isClosedEmbedding.injective, hfactor⟩

end NormalProjectiveSurface

end KltDP.Geometry
