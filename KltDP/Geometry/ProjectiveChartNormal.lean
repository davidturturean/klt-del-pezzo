import KltDP.Geometry.ProjectiveChart
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Normality of the first standard projective chart

The degree-zero localization at the first homogeneous coordinate is the
actual chart ring constructed in `ProjectiveChart`. Its coordinate-ring
equivalence with a polynomial ring proves integral closedness. The actual
prime localizations and structure-sheaf stalks are consequently integrally
closed domains.

The scheme statements concern the open set where the first coordinate is
nonzero. Covering projective space by all coordinate charts, and proving its
dimension, are separate steps; neither is an assumption of these results.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

/-- Integral closedness transports along an actual ring equivalence. The
equivalence gives the algebra structure of a localization at the units. -/
theorem isIntegrallyClosed_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsIntegrallyClosed R] (e : R ≃+* S) :
    IsIntegrallyClosed S := by
  letI : Algebra R S := (e : R →+* S).toAlgebra
  letI : IsLocalization (⊥ : Submonoid R) R :=
    IsLocalization.at_units _ bot_le
  let e' : R ≃ₐ[R] S := { e with commutes' := fun _ ↦ rfl }
  letI : IsLocalization (⊥ : Submonoid R) S :=
    IsLocalization.isLocalization_of_algEquiv (⊥ : Submonoid R) e'
  exact isIntegrallyClosed_of_isLocalization S (⊥ : Submonoid R) bot_le

/-- The actual spectrum of an integrally closed domain is normal: its
stalks are the existing localizations at prime ideals. -/
theorem spec_isNormalScheme_of_isIntegrallyClosed
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalScheme (Spec (CommRingCat.of R)) := by
  intro p
  letI : IsDomain (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isDomain_of_local_atPrime p.isPrime
  letI : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
    isIntegrallyClosed_of_isLocalization
      (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors
  let e : (Spec (CommRingCat.of R)).presheaf.stalk p ≃+*
      Localization.AtPrime p.asIdeal :=
    (StructureSheaf.stalkIso R p).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain (Localization.AtPrime p.asIdeal) e.toMulEquiv,
    isIntegrallyClosed_of_ringEquiv e.symm⟩

/-- Normality restricts along an actual open immersion, using its actual
isomorphisms on structure-sheaf stalks. -/
theorem isNormalScheme_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (hY : IsNormalScheme Y) :
    IsNormalScheme X := by
  intro x
  letI : IsDomain (Y.presheaf.stalk (f.base x)) := (hY (f.base x)).1
  letI : IsIntegrallyClosed (Y.presheaf.stalk (f.base x)) := (hY (f.base x)).2
  let e : Y.presheaf.stalk (f.base x) ≃+* X.presheaf.stalk x :=
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain (Y.presheaf.stalk (f.base x)) e.symm.toMulEquiv,
    isIntegrallyClosed_of_ringEquiv e⟩

/-- An open immersion also identifies normal source stalks with target
stalks at points of its image. -/
theorem normal_stalk_at_image_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (hX : IsNormalScheme X) (x : X) :
    IsDomain (Y.presheaf.stalk (f.base x)) ∧
      IsIntegrallyClosed (Y.presheaf.stalk (f.base x)) := by
  letI : IsDomain (X.presheaf.stalk x) := (hX x).1
  letI : IsIntegrallyClosed (X.presheaf.stalk x) := (hX x).2
  let e : Y.presheaf.stalk (f.base x) ≃+* X.presheaf.stalk x :=
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain (X.presheaf.stalk x) e.toMulEquiv,
    isIntegrallyClosed_of_ringEquiv e.symm⟩

namespace ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- Polynomial rings over fields are integrally closed by unique
factorization and the integral-root theorem. -/
theorem affineRing_isIntegrallyClosed : IsIntegrallyClosed (affineRing k n) := by
  infer_instance

/-- The degree-zero localization defining the chart is a domain through
its actual coordinate-ring equivalence. -/
theorem chartRing_isDomain : IsDomain (chartRing k n) :=
  MulEquiv.isDomain (affineRing k n) (coordinateRingEquiv k n).toMulEquiv

/-- Integral closedness of the actual chart ring follows from the proved
dehomogenization equivalence, with no dimension premise. -/
theorem chartRing_isIntegrallyClosed : IsIntegrallyClosed (chartRing k n) := by
  letI : IsIntegrallyClosed (affineRing k n) := affineRing_isIntegrallyClosed k n
  exact isIntegrallyClosed_of_ringEquiv (coordinateRingEquiv k n).symm

/-- Every actual prime localization of the chart ring is an integrally
closed domain. -/
theorem chartLocalization_normal (p : PrimeSpectrum (chartRing k n)) :
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  letI : IsDomain (chartRing k n) := chartRing_isDomain k n
  letI : IsIntegrallyClosed (chartRing k n) := chartRing_isIntegrallyClosed k n
  exact ⟨IsLocalization.isDomain_of_local_atPrime p.isPrime,
    isIntegrallyClosed_of_isLocalization
      (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors⟩

/-- The affine scheme whose coordinate ring is the degree-zero
localization is normal. -/
theorem chartSpec_isNormalScheme :
    IsNormalScheme (Spec (CommRingCat.of (chartRing k n))) := by
  letI : IsDomain (chartRing k n) := chartRing_isDomain k n
  letI : IsIntegrallyClosed (chartRing k n) := chartRing_isIntegrallyClosed k n
  exact spec_isNormalScheme_of_isIntegrallyClosed (chartRing k n)

/-- The actual standard-chart open immersion supplied by `Proj`. -/
def chartMorphism : Spec (CommRingCat.of (chartRing k n)) ⟶ projectiveSpace k n :=
  Proj.awayι (grading k n) (coordinate k n)
    (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 1))) (by decide)

instance : IsOpenImmersion (chartMorphism k n) := by
  unfold chartMorphism
  infer_instance

theorem chartMorphism_opensRange :
    (chartMorphism k n).opensRange = Proj.basicOpen (grading k n) (coordinate k n) :=
  Proj.opensRange_awayι (grading k n) (coordinate k n)
    (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 1))) (by decide)

/-- The restriction of actual projective space to `X₀ ≠ 0` is normal. -/
theorem firstStandardOpen_isNormalScheme :
    IsNormalScheme (Proj.basicOpen (grading k n) (coordinate k n)).toScheme :=
  isNormalScheme_of_isOpenImmersion
    (Proj.basicOpenIsoSpec (grading k n) (coordinate k n)
      (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 1))) (by decide)).hom
    (chartSpec_isNormalScheme k n)

/-- Every projective-space stalk in this chart is an integrally closed
domain, through the actual open immersion and its stalk isomorphisms. -/
theorem projectiveSpace_stalk_normal_of_mem_firstStandardOpen
    (x : projectiveSpace k n)
    (hx : x ∈ Proj.basicOpen (grading k n) (coordinate k n)) :
    IsDomain ((projectiveSpace k n).presheaf.stalk x) ∧
      IsIntegrallyClosed ((projectiveSpace k n).presheaf.stalk x) := by
  exact normal_stalk_at_image_of_isOpenImmersion
    (Proj.basicOpen (grading k n) (coordinate k n)).ι
    (firstStandardOpen_isNormalScheme k n) ⟨x, hx⟩

end ProjectiveChart

end KltDP.Geometry
