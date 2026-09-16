import KltDP.Geometry.ProjectiveSpaceNormal
import KltDP.Geometry.ProjectiveSpaceIntegral
import KltDP.Topology.DimensionOpenCover
import Mathlib.RingTheory.Ideal.Height

/-!
# Projective-space dimension from polynomial-ring dimension

All geometric adapters are proved here using the actual coordinate rings,
the actual standard affine cover, and the underlying homeomorphisms of
scheme isomorphisms. The polynomial-ring dimension statement remains an
explicit hypothesis.

A separate algebraic adapter derives global ring dimension from the common
dimension of all maximal localizations. Thus the dimension clause of
Stacks, Tag 00OP, is sufficient as a literal external input; no external
input is declared in this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Topology

universe u

namespace KltDP.Geometry

/-- If every maximal localization of a nonzero commutative ring has the
same dimension, that number is its global Krull dimension. The proof uses
actual prime heights and existence of containing maximal ideals. -/
theorem ringKrullDim_eq_of_maximal_localizations
    (R : Type*) [CommRing R] [Nontrivial R] (d : WithBot ℕ∞)
    (hloc : ∀ (M : Ideal R) [M.IsMaximal],
      ringKrullDim (Localization.AtPrime M) = d) :
    ringKrullDim R = d := by
  apply le_antisymm
  · rw [ringKrullDim, Order.krullDim_eq_iSup_height]
    refine iSup_le fun P ↦ ?_
    letI : P.asIdeal.IsPrime := P.isPrime
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
    letI : M.IsMaximal := hM
    calc
      (Order.height P : WithBot ℕ∞) = (P.asIdeal.height : WithBot ℕ∞) := by
        rw [Ideal.height_eq_primeHeight]
        rfl
      _ ≤ (M.height : WithBot ℕ∞) := by
        exact_mod_cast Ideal.height_mono hPM
      _ = ringKrullDim (Localization.AtPrime M) :=
        (IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M)).symm
      _ = d := hloc M
  · obtain ⟨M, hM⟩ := Ideal.exists_maximal R
    letI : M.IsMaximal := hM
    rw [← hloc M,
      IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M)]
    exact Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top

/-- The dimension-only clause of the maximal-localization statement for
a polynomial ring implies the required polynomial-ring dimension. -/
theorem polynomial_ringKrullDim_of_maximal_localizations
    (k : Type u) [Field k] (n : ℕ)
    (hloc : ∀ (M : Ideal (MvPolynomial (Fin n) k)) [M.IsMaximal],
      ringKrullDim (Localization.AtPrime M) = (n : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) :=
  ringKrullDim_eq_of_maximal_localizations (MvPolynomial (Fin n) k) n hloc

namespace ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual chart ring has the dimension of the ordinary polynomial
ring via the proved permutation and dehomogenization equivalences. -/
theorem coordinateChartRing_ringKrullDim
    (hdim : ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞))
    (i : Fin (n + 1)) :
    ringKrullDim (coordinateChartRing k n i) = (n : WithBot ℕ∞) :=
  (ringKrullDim_eq_of_ringEquiv
    ((firstChartEquivCoordinateChart k n i).symm.trans (coordinateRingEquiv k n))).trans hdim

/-- The underlying topology of an actual standard open has the
dimension of its actual affine coordinate ring. -/
theorem coordinateStandardOpen_topologicalKrullDim
    (hdim : ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞))
    (i : Fin (n + 1)) :
    topologicalKrullDim
      (Proj.basicOpen (grading k n) (MvPolynomial.X i)).toScheme = (n : WithBot ℕ∞) := by
  let e := Proj.basicOpenIsoSpec (grading k n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i) (by decide)
  calc
    _ = topologicalKrullDim (Spec (CommRingCat.of (coordinateChartRing k n i))) :=
      IsHomeomorph.topologicalKrullDim_eq e.schemeIsoToHomeo
        e.schemeIsoToHomeo.isHomeomorph
    _ = ringKrullDim (coordinateChartRing k n i) :=
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (coordinateChartRing k n i)
    _ = n := coordinateChartRing_ringKrullDim k n hdim i

end ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual projective `n`-space has dimension `n` provided the ordinary
polynomial ring in `n` variables has dimension `n`. The upper bound uses
the proved open-cover theorem; the lower bound uses one actual chart. -/
theorem projectiveSpace_topologicalKrullDim_of_polynomial_dimension
    (k : Type u) [Field k] (n : ℕ)
    (hdim : ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞)) :
    topologicalKrullDim (projectiveSpace k n) = (n : WithBot ℕ∞) := by
  apply le_antisymm
  · refine KltDP.Topology.topologicalKrullDim_le_of_open_cover
      (fun i : Fin (n + 1) ↦
        Proj.basicOpen (ProjectiveChart.grading k n) (MvPolynomial.X i))
      ?_ (n : WithBot ℕ∞) ?_
    · intro x
      exact TopologicalSpace.Opens.mem_iSup.mp
        ((ProjectiveChart.iSup_coordinateStandardOpen k n).ge (Set.mem_univ x))
    · intro i
      exact (ProjectiveChart.coordinateStandardOpen_topologicalKrullDim k n hdim i).le
  · calc
      (n : WithBot ℕ∞) = topologicalKrullDim
          (Proj.basicOpen (ProjectiveChart.grading k n)
            (MvPolynomial.X (0 : Fin (n + 1)))).toScheme :=
        (ProjectiveChart.coordinateStandardOpen_topologicalKrullDim k n hdim 0).symm
      _ ≤ topologicalKrullDim (projectiveSpace k n) :=
        KltDP.Topology.topologicalKrullDim_opens_le _

/-- The existing projective plane, with its actual structure morphism,
is a normal projective surface once the explicit two-variable polynomial
dimension input is supplied. No geometric property is postulated. -/
def projectivePlaneSurfaceOfPolynomialDimension
    (k : Type u) [Field k]
    (hdim : ringKrullDim (MvPolynomial (Fin 2) k) = (2 : WithBot ℕ∞)) :
    NormalProjectiveSurface k where
  toScheme := projectiveSpace k 2
  structureMorphism := projectiveSpaceToSpec k 2
  integral := projectiveSpace_isIntegral k 2
  normal := projectiveSpace_isNormalScheme k 2
  projective := projectiveSpace_isProjectiveOverField k 2
  dimension_two := projectiveSpace_topologicalKrullDim_of_polynomial_dimension k 2 hdim

end KltDP.Geometry
