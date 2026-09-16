import KltDP.Geometry.SurfaceRiemannRochSource
import KltDP.Geometry.HodgeIndexReduction
import KltDP.Geometry.AmpleSelfIntersectionPositive
import KltDP.Geometry.AmplePositivity
import KltDP.Geometry.ProjectiveAmpleWitness

/-!
# Full integral Hodge-index source and original Picard consumers

Independently proved source adapters for Hartshorne V, Theorem 1.9.
There is no axiom in this file. The raw statement retains arbitrary integral
divisors on the original regular integral projective surface, an actual ample
divisor, nontriviality modulo numerical equivalence, and orthogonality.
It asserts strict negativity, not finite dimensionality or a signature on a
surrogate vector space. Normality is derived from the original regularity.

The separately proved consumers use the existing Cartier--Weil equivalence,
the actual Picard pairing and its numerical kernel. Positive self-intersection
of the original ample sheaf is supplied by the already compiled geometric
producer, rather than by another source premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SurfaceRiemannRochSource

universe u

namespace KltDP.Geometry.SurfaceHodgeIndexSource

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The original divisor line sheaf, with the proved Cartier inverse. -/
def divisorLine (D : X.WeilDivisor) : InvertibleSheaf X.toScheme :=
  cartierDivisorInvertibleSheaf X.toScheme
    ((X.regularCartierWeilEquiv hregular).symm D)

/-- Numerical zero means zero degree on every actual prime curve. -/
def NumericallyZero (D : X.WeilDivisor) : Prop :=
  X.NumericallyTrivial (cartierPicardClass X.toScheme
    ((X.regularCartierWeilEquiv hregular).symm D))

/-- The original integral surface intersection, with no rational quotient. -/
def divisorPairing (D E : X.WeilDivisor) : ℤ :=
  intersectionPairing X hregular
    ((X.regularCartierWeilEquiv hregular).symm D)
    ((X.regularCartierWeilEquiv hregular).symm E)

/-- The source's test against every divisor is equivalent to the existing
prime-curve numerical test, on the original objects. -/
theorem numericallyZero_iff_all_pairings (D : X.WeilDivisor) :
    NumericallyZero X hregular D ↔
      ∀ E : X.WeilDivisor, divisorPairing X hregular D E = 0 := by
  constructor
  · intro h E
    exact X.intersectionPairing_eq_zero_of_numericallyTrivial_left hregular _ _ h
  · intro h C
    rw [← X.picardPairing_primeCurveClass hregular
      (cartierPicardClass X.toScheme ((X.regularCartierWeilEquiv hregular).symm D)) C,
      X.picardPairing_class hregular]
    have hC := h ((X.regularCartierWeilEquiv hregular) (X.primeCurveCartier hregular C))
    simpa only [divisorPairing, AddEquiv.symm_apply_apply] using hC

/-- The full standalone strict integral-divisor statement, still hypothetical. -/
def RawStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
    (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
    (hdimension : topologicalKrullDim Y = 2)
    (hregular : ∀ y : Y, RegularPoint Y y),
    let X := sourceSurface Y f hIntegral hprojective hdimension hregular
    ∀ H D : X.WeilDivisor,
      AmpleSerre.IsAmple (divisorLine X hregular H) →
      (¬ ∀ E : X.WeilDivisor, divisorPairing X hregular D E = 0) →
      divisorPairing X hregular D H = 0 →
      divisorPairing X hregular D D < 0

/-- The raw theorem keeps the original scheme and map under specialization. -/
theorem raw_apply (raw : RawStatement.{u}) (H D : X.WeilDivisor)
    (hH : AmpleSerre.IsAmple (divisorLine X hregular H))
    (hD : ¬ NumericallyZero X hregular D)
    (hperp : divisorPairing X hregular D H = 0) :
    divisorPairing X hregular D D < 0 :=
  raw k X.toScheme X.structureMorphism X.integral X.projective X.dimension_two
    hregular H D hH
      (fun hall => hD ((numericallyZero_iff_all_pairings X hregular D).mpr hall)) hperp

/-- Every original Cartier divisor is transported through the proved
Cartier--Weil equivalence; no restricted divisor family is assumed. -/
theorem cartier_neg_of_orthogonal (raw : RawStatement.{u})
    (H D : CartierDivisor X.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H))
    (hD : ¬ X.NumericallyTrivial (cartierPicardClass X.toScheme D))
    (hperp : intersectionPairing X hregular D H = 0) :
    intersectionPairing X hregular D D < 0 := by
  have h := raw_apply X hregular raw
    ((X.regularCartierWeilEquiv hregular) H)
    ((X.regularCartierWeilEquiv hregular) D)
  simp only [divisorLine, NumericallyZero, divisorPairing,
    AddEquiv.symm_apply_apply] at h
  exact h hH hD hperp

/-- Strict negativity for any actual nontrivial integral Picard class
orthogonal to the class of an actual ample invertible sheaf. -/
theorem picard_neg_of_orthogonal (raw : RawStatement.{u})
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L)
    (p : X.toScheme.Pic)
    (hperp : X.picardPairing hregular L.toPic p = 0)
    (hp : ¬ X.NumericallyTrivial p) :
    X.picardPairing hregular p p < 0 := by
  obtain ⟨H, hH⟩ := cartierPicardClass_surjective X.toScheme L.toPic
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X.toScheme p
  have hHample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H) :=
    AmplePositivity.isAmple_of_toPic_eq hH.symm hL
  rw [← hH, X.picardPairing_class hregular H D] at hperp
  rw [X.picardPairing_class hregular D D]
  exact cartier_neg_of_orthogonal X hregular raw H D hHample hp
    ((X.intersectionPairing_symm hregular D H).trans hperp)

/-- The missing semidefinite input is derived for every original ample
class, including the numerical-zero branch by the proved pairing kernel. -/
theorem semidefinite_of_isAmple (raw : RawStatement.{u})
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L) :
    X.HodgeIndexSemidefinite hregular L.toPic := by
  intro p hperp
  by_cases hp : X.NumericallyTrivial p
  · exact le_of_eq (X.picardPairing_eq_zero_of_numericallyTrivial hregular p p hp)
  · exact le_of_lt (picard_neg_of_orthogonal X hregular raw L hL p hperp hp)

/-- The actual positive-square producer closes the existing signature
statement as soon as an actual ample sheaf is given. No square premise remains. -/
theorem signature_of_isAmple (raw : RawStatement.{u})
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L) :
    X.HodgeIndexSignature hregular :=
  ⟨L.toPic,
    AmpleSelfIntersectionPositive.selfIntersection_pos_of_isAmple X hregular L hL,
    semidefinite_of_isAmple X hregular raw L hL⟩

/-- The original projective embedding constructs the ample witness, so the
existing Hodge statement now has no supplied polarization or positive-square
hypothesis. The published Hodge theorem is still the explicit raw parameter. -/
theorem signature (raw : RawStatement.{u}) : X.HodgeIndexSignature hregular := by
  obtain ⟨L, hL⟩ := X.exists_isAmple
  exact signature_of_isAmple X hregular raw L hL

end KltDP.Geometry.SurfaceHodgeIndexSource

