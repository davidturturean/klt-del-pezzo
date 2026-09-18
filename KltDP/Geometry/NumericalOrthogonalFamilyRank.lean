import KltDP.Geometry.NumericalIntersectionPairing
import KltDP.Geometry.SurfaceNumericalFinitenessProved
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Fintype.Option

/-!
# Orthogonal negative numerical classes bound the original Picard rank

The actual numerical intersection form has nonzero diagonal on a family of
strictly negative classes, and on an orthogonal positive class adjoined to it.
Mathlib's orthogonal-family theorem proves linear independence from these
pairings. Its dimension theorem then bounds the size of the extended family
by the original `picardRank`.

The first rank bound takes the existing numerical finite-dimensionality
statement explicitly. The regular-surface wrapper supplies it from the
separately proved integral numerical finiteness theorem.
-/

noncomputable section

open AlgebraicGeometry

universe u v

namespace KltDP.Geometry.NumericalOrthogonalFamilyRank

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  {ι : Type v}

/-- Adjoin the actual positive class to the given original numerical classes. -/
def positiveExtension (h : X.NumericalClassGroup) (c : ι → X.NumericalClassGroup) :
    Option ι → X.NumericalClassGroup
  | none => h
  | some i => c i

/-- Orthogonality and strictly negative diagonal pairings prove independence;
no independence premise is assumed. -/
theorem negativeFamily_linearIndependent (c : ι → X.NumericalClassGroup)
    (horth : ∀ i j, i ≠ j → X.numericalIntersectionBilinForm hregular (c i) (c j) = 0)
    (hneg : ∀ i, X.numericalIntersectionBilinForm hregular (c i) (c i) < 0) :
    LinearIndependent ℚ c :=
  LinearMap.BilinForm.linearIndependent_of_iIsOrtho horth (fun i => ne_of_lt (hneg i))

/-- A positive class orthogonal to the negative family increases its independent
size by one, on the same original numerical quotient. -/
theorem positiveExtension_linearIndependent (h : X.NumericalClassGroup)
    (c : ι → X.NumericalClassGroup)
    (hpos : 0 < X.numericalIntersectionBilinForm hregular h h)
    (horth : ∀ i j, i ≠ j → X.numericalIntersectionBilinForm hregular (c i) (c j) = 0)
    (hneg : ∀ i, X.numericalIntersectionBilinForm hregular (c i) (c i) < 0)
    (hperp : ∀ i, X.numericalIntersectionBilinForm hregular h (c i) = 0) :
    LinearIndependent ℚ (positiveExtension X h c) := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho
    (B := X.numericalIntersectionBilinForm hregular)
  · intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j => exact hperp j
    | some i =>
        cases j with
        | none =>
            exact (LinearMap.BilinForm.IsSymm.eq
              (X.numericalIntersectionBilinForm_isSymm hregular) (c i) h).trans (hperp i)
        | some j => exact horth i j (fun heq => hij (congrArg Option.some heq))
  · intro i
    cases i with
    | none => exact ne_of_gt hpos
    | some i => exact ne_of_lt (hneg i)

/-- The orthogonal negative family and one positive direction fit inside the
original finite-dimensional numerical space. -/
theorem card_add_one_le_picardRank_of_finite [Fintype ι]
    (hfinite : X.NumericalSpaceFiniteDimensional)
    (h : X.NumericalClassGroup) (c : ι → X.NumericalClassGroup)
    (hpos : 0 < X.numericalIntersectionBilinForm hregular h h)
    (horth : ∀ i j, i ≠ j → X.numericalIntersectionBilinForm hregular (c i) (c j) = 0)
    (hneg : ∀ i, X.numericalIntersectionBilinForm hregular (c i) (c i) < 0)
    (hperp : ∀ i, X.numericalIntersectionBilinForm hregular h (c i) = 0) :
    Fintype.card ι + 1 ≤ X.picardRank := by
  letI : FiniteDimensional ℚ X.NumericalClassGroup := hfinite
  have hli := positiveExtension_linearIndependent X hregular h c hpos horth hneg hperp
  change Fintype.card ι + 1 ≤ Module.finrank ℚ X.NumericalClassGroup
  simpa only [Fintype.card_option] using hli.fintype_card_le_finrank

/-- On a regular projective surface the numerical finiteness input is supplied
internally, while all family classes and geometric pairing hypotheses remain
the original ones. -/
theorem card_add_one_le_picardRank [Fintype ι]
    (h : X.NumericalClassGroup) (c : ι → X.NumericalClassGroup)
    (hpos : 0 < X.numericalIntersectionBilinForm hregular h h)
    (horth : ∀ i j, i ≠ j → X.numericalIntersectionBilinForm hregular (c i) (c j) = 0)
    (hneg : ∀ i, X.numericalIntersectionBilinForm hregular (c i) (c i) < 0)
    (hperp : ∀ i, X.numericalIntersectionBilinForm hregular h (c i) = 0) :
    Fintype.card ι + 1 ≤ X.picardRank :=
  card_add_one_le_picardRank_of_finite X hregular
    (SurfaceNumericalFinitenessProved.numericalSpaceFiniteDimensional X hregular)
    h c hpos horth hneg hperp

end KltDP.Geometry.NumericalOrthogonalFamilyRank
