import KltDP.Geometry.SmoothCanonicalCartierExterior
import KltDP.Geometry.SmoothSurfaceDivisorPicard
import KltDP.Geometry.IntersectionPairingSymmetry
import KltDP.Geometry.SectionEffectiveWeil
import KltDP.Geometry.SurfaceEulerSections
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Linarith

/-!
# Original objects and specialization proofs for Hartshorne V.1.6

This file declares no literature axiom. `RawStatement` is the full displayed
three-term formula, on arbitrary original integral projective regular
surfaces over an algebraically closed field and arbitrary integral divisors.
The normal-surface packaging is constructed from regularity. The canonical
condition is the actual divisor-sheaf isomorphism with the intrinsic second
exterior power of relative differentials; smoothness is not a raw premise.

The consumers keep `raw` explicit. They produce original nonzero sections
and effective integral Weil divisors from complementary-section vanishing
and positivity of the displayed numerical expression. They do not assert
surface Riemann--Roch, top-cohomology duality, or either vanishing premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SmoothCanonicalExteriorComparison
open KltDP.Geometry.SmoothCanonicalCartierRepresentative
open KltDP.Geometry.SmoothCanonicalCartierExterior

universe u

namespace KltDP.Geometry.SurfaceRiemannRochSource

variable {k : Type u} [Field k]

/-- Package the source's original scheme and structure map. The normality
field follows from the existing regular-local factoriality theorem. -/
def sourceSurface (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
    (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
    (hdimension : topologicalKrullDim Y = 2)
    (hregular : ∀ y : Y, RegularPoint Y y) : NormalProjectiveSurface k where
  toScheme := Y
  structureMorphism := f
  integral := hIntegral
  normal y := by
    obtain ⟨hD, hU⟩ :=
      regularPoint_stalk_isDomain_and_uniqueFactorizationMonoid Y y (hregular y)
    letI : IsDomain (Y.presheaf.stalk y) := hD
    letI : UniqueFactorizationMonoid (Y.presheaf.stalk y) := hU
    exact ⟨hD, UniqueFactorizationMonoid.instIsIntegrallyClosed⟩
  projective := hprojective
  dimension_two := hdimension

variable [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The original O(D), using the proved Cartier inverse of the original
integral Weil divisor. -/
def divisorModule (D : X.WeilDivisor) : X.toScheme.Modules :=
  cartierDivisorModule X.toScheme ((X.regularCartierWeilEquiv hregular).symm D)

/-- The dimension of the actual scalar-correct sheaf cohomology group. -/
def hDimension (D : X.WeilDivisor) (i : ℕ) : ℕ :=
  cohomologyDimension X.structureMorphism (divisorModule X hregular D) i

/-- The arithmetic genus as defined immediately before Hartshorne V.1.6. -/
def arithmeticGenus : ℤ :=
  eulerCharacteristic X.structureMorphism
    (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) - 1

/-- The full right-hand side, retaining the actual intersection of D with
D-K and the source's arithmetic-genus term. -/
def rrNumber (D K : X.WeilDivisor) : ℚ :=
  (intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm D)
      ((X.regularCartierWeilEquiv hregular).symm (D - K)) : ℚ) / 2 +
    1 + (arithmeticGenus X : ℚ)

/-- The source's definition of a canonical divisor: its original divisor
sheaf is the intrinsic exterior square of the original differential sheaf. -/
def IsCanonical (K : X.WeilDivisor) : Prop :=
  Nonempty (divisorModule X hregular K ≅
    relativeDifferentialExterior X.structureMorphism 2)

/-- The full displayed published formula as a hypothetical parameter.
There is no smoothness or supplied normality premise, and D and K range over
all original integral Weil divisors of the source scheme. -/
def RawStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
    (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
    (hdimension : topologicalKrullDim Y = 2)
    (hregular : ∀ y : Y, RegularPoint Y y),
    let X := sourceSurface Y f hIntegral hprojective hdimension hregular
    ∀ D K : X.WeilDivisor, IsCanonical X hregular K →
      (hDimension X hregular D 0 : ℚ) - (hDimension X hregular D 1 : ℚ) +
        (hDimension X hregular (K - D) 0 : ℚ) = rrNumber X hregular D K

/-- Applying the raw statement preserves the given original surface. -/
theorem raw_apply (raw : RawStatement.{u}) (D K : X.WeilDivisor)
    (hK : IsCanonical X hregular K) :
    (hDimension X hregular D 0 : ℚ) - (hDimension X hregular D 1 : ℚ) +
      (hDimension X hregular (K - D) 0 : ℚ) = rrNumber X hregular D K :=
  raw k X.toScheme X.structureMorphism X.integral X.projective X.dimension_two
    hregular D K hK

/-- The full three-term formula produces an original nonzero section from
actual complementary-section vanishing and a positive displayed right side. -/
theorem exists_nonzero_section (raw : RawStatement.{u}) (D K : X.WeilDivisor)
    (hK : IsCanonical X hregular K)
    (hvanish : Subsingleton (sections (divisorModule X hregular (K - D))))
    (hpositive : 0 < rrNumber X hregular D K) :
    ∃ s : sections (divisorModule X hregular D), s ≠ 0 := by
  have heq := raw_apply X hregular raw D K hK
  have hzero : hDimension X hregular (K - D) 0 = 0 := by
    letI := baseSectionsModule X.structureMorphism (divisorModule X hregular (K - D))
    letI : Subsingleton (sections (divisorModule X hregular (K - D))) := hvanish
    change cohomologyDimension X.structureMorphism (divisorModule X hregular (K - D)) 0 = 0
    rw [cohomologyDimension_zero_eq_finrank_sections]
    exact Module.finrank_zero_of_subsingleton
  have hnonnegative : (0 : ℚ) ≤ hDimension X hregular D 1 := Nat.cast_nonneg _
  have hpositiveQ : (0 : ℚ) < hDimension X hregular D 0 := by
    rw [hzero, Nat.cast_zero, add_zero] at heq
    have hsub : (0 : ℚ) <
        (hDimension X hregular D 0 : ℚ) - (hDimension X hregular D 1 : ℚ) := by
      rw [heq]
      exact hpositive
    exact lt_of_lt_of_le hsub (sub_le_self _ hnonnegative)
  have hpositiveNat : 0 < hDimension X hregular D 0 := by
    exact_mod_cast hpositiveQ
  letI := baseSectionsModule X.structureMorphism (divisorModule X hregular D)
  have hdimension : cohomologyDimension X.structureMorphism (divisorModule X hregular D) 0 =
      Module.finrank k (sections (divisorModule X hregular D)) :=
    cohomologyDimension_zero_eq_finrank_sections X.structureMorphism
      (divisorModule X hregular D)
  have hfinrank : 0 < Module.finrank k (sections (divisorModule X hregular D)) := by
    rw [← hdimension]
    exact hpositiveNat
  letI : Nontrivial (sections (divisorModule X hregular D)) :=
    Module.nontrivial_of_finrank_pos hfinrank
  exact exists_ne (0 : sections (divisorModule X hregular D))

/-- The nonzero section supplies a finite effective integral Weil divisor
linearly equivalent to the original D through the existing actual producer. -/
theorem exists_effectiveWeil (raw : RawStatement.{u}) (D K : X.WeilDivisor)
    (hK : IsCanonical X hregular K)
    (hvanish : Subsingleton (sections (divisorModule X hregular (K - D))))
    (hpositive : 0 < rrNumber X hregular D K) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧ X.LinearlyEquivalent Z D := by
  obtain ⟨s, hs⟩ := exists_nonzero_section X hregular raw D K hK hvanish hpositive
  exact X.exists_effectiveWeil_of_nonzero_section hregular D s hs

section SmoothConsumer

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- The constructed original canonical Weil representative satisfies the
source's canonical condition by the compiled intrinsic exterior comparison. -/
theorem constructedCanonical_isCanonical :
    IsCanonical X X.regularPoints_of_isSmooth (weilRepresentative X) := by
  let K := cartierRepresentative X.structureMorphism
  have hK : (X.regularCartierWeilEquiv X.regularPoints_of_isSmooth).symm
      (X.cartierToWeilHom K) = K :=
    (X.regularCartierWeilEquiv X.regularPoints_of_isSmooth).symm_apply_apply K
  change Nonempty (cartierDivisorModule X.toScheme
    ((X.regularCartierWeilEquiv X.regularPoints_of_isSmooth).symm
      (X.cartierToWeilHom K)) ≅ relativeDifferentialExterior X.structureMorphism 2)
  rw [hK]
  exact ⟨representativeIsoExterior X.structureMorphism⟩

/-- The actual smooth-surface canonical representative specializes the full
raw formula; regularity and the canonical comparison are proved internally. -/
theorem exists_effectiveWeil_of_constructedCanonical (raw : RawStatement.{u})
    (D : X.WeilDivisor)
    (hvanish : Subsingleton (sections (divisorModule X X.regularPoints_of_isSmooth
      (weilRepresentative X - D))))
    (hpositive : 0 < rrNumber X X.regularPoints_of_isSmooth D (weilRepresentative X)) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧ X.LinearlyEquivalent Z D :=
  exists_effectiveWeil X X.regularPoints_of_isSmooth raw D (weilRepresentative X)
    (constructedCanonical_isCanonical X) hvanish hpositive

end SmoothConsumer

end KltDP.Geometry.SurfaceRiemannRochSource

