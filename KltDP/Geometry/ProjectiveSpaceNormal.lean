import KltDP.Geometry.ProjectiveChartNormal
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Normality of actual projective space

A permutation of the homogeneous variables induces inverse maps on the
degree-zero localization rings. Thus every coordinate chart has the
integrally closed coordinate ring already proved for the first chart.
The coordinate variables span the irrelevant ideal, so their actual
affine charts cover projective space. Stalk isomorphisms for these open
immersions prove normality of the existing `Proj` scheme.

No dimension statement is assumed or proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

/-- A degree-preserving ring equivalence gives an equivalence of the
actual homogeneous localizations when it preserves their denominator
submonoids in both directions. -/
def homogeneousLocalizationRingEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]
    (P : Submonoid A) (Q : Submonoid B) (e : A ≃+* B)
    (hPQ : P ≤ Q.comap (e : A →+* B))
    (hQP : Q ≤ P.comap (e.symm : B →+* A))
    (he : ∀ d a, a ∈ 𝒜 d → e a ∈ ℬ d)
    (he' : ∀ d b, b ∈ ℬ d → e.symm b ∈ 𝒜 d) :
    HomogeneousLocalization 𝒜 P ≃+* HomogeneousLocalization ℬ Q where
  __ := HomogeneousLocalization.map 𝒜 ℬ (e : A →+* B) hPQ he
  invFun := HomogeneousLocalization.map ℬ 𝒜 (e.symm : B →+* A) hQP he'
  left_inv z := by
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
    apply congrArg (HomogeneousLocalization.mk (𝒜 := 𝒜) (x := P))
    apply HomogeneousLocalization.NumDenSameDeg.ext (x := P)
    · rfl
    · exact e.symm_apply_apply (c.num : A)
    · exact e.symm_apply_apply (c.den : A)
  right_inv z := by
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
    apply congrArg (HomogeneousLocalization.mk (𝒜 := ℬ) (x := Q))
    apply HomogeneousLocalization.NumDenSameDeg.ext (x := Q)
    · rfl
    · exact e.apply_symm_apply (c.num : B)
    · exact e.apply_symm_apply (c.den : B)

namespace ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual degree-zero localization at coordinate `i`. -/
abbrev coordinateChartRing (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading k n)
    (MvPolynomial.X i : homogeneousRing k n)

/-- Swapping `X₀` and `Xᵢ` gives an actual equivalence from the first
coordinate chart ring to the `i`th chart ring. -/
def firstChartEquivCoordinateChart (i : Fin (n + 1)) :
    chartRing k n ≃+* coordinateChartRing k n i := by
  refine homogeneousLocalizationRingEquiv (grading k n) (grading k n)
    (Submonoid.powers (coordinate k n))
    (Submonoid.powers (MvPolynomial.X i : homogeneousRing k n))
    (MvPolynomial.renameEquiv k (Equiv.swap 0 i)).toRingEquiv ?_ ?_ ?_ ?_
  · apply Submonoid.powers_le.mpr
    change MvPolynomial.rename (Equiv.swap 0 i) (MvPolynomial.X 0) ∈
      Submonoid.powers (MvPolynomial.X i : homogeneousRing k n)
    rw [MvPolynomial.rename_X, Equiv.swap_apply_left]
    exact Submonoid.mem_powers _
  · apply Submonoid.powers_le.mpr
    change MvPolynomial.rename (Equiv.swap 0 i) (MvPolynomial.X i) ∈
      Submonoid.powers (MvPolynomial.X 0 : homogeneousRing k n)
    rw [MvPolynomial.rename_X, Equiv.swap_apply_right]
    exact Submonoid.mem_powers _
  · intro d a ha
    change (MvPolynomial.rename (Equiv.swap 0 i) a).IsHomogeneous d
    exact (show a.IsHomogeneous d from ha).rename_isHomogeneous
  · intro d a ha
    change (MvPolynomial.rename (Equiv.swap 0 i) a).IsHomogeneous d
    exact (show a.IsHomogeneous d from ha).rename_isHomogeneous

/-- Every coordinate chart ring is a domain. -/
theorem coordinateChartRing_isDomain (i : Fin (n + 1)) :
    IsDomain (coordinateChartRing k n i) := by
  letI : IsDomain (chartRing k n) := chartRing_isDomain k n
  exact MulEquiv.isDomain (chartRing k n)
    (firstChartEquivCoordinateChart k n i).symm.toMulEquiv

/-- Every coordinate chart ring is integrally closed, through the actual
variable permutation rather than an assumed chart isomorphism. -/
theorem coordinateChartRing_isIntegrallyClosed (i : Fin (n + 1)) :
    IsIntegrallyClosed (coordinateChartRing k n i) := by
  letI : IsDomain (chartRing k n) := chartRing_isDomain k n
  letI : IsIntegrallyClosed (chartRing k n) := chartRing_isIntegrallyClosed k n
  exact isIntegrallyClosed_of_ringEquiv (firstChartEquivCoordinateChart k n i)

/-- Each member of the standard affine cover is normal. -/
theorem coordinateChartSpec_isNormalScheme (i : Fin (n + 1)) :
    IsNormalScheme (Spec (CommRingCat.of (coordinateChartRing k n i))) := by
  letI : IsDomain (coordinateChartRing k n i) := coordinateChartRing_isDomain k n i
  letI : IsIntegrallyClosed (coordinateChartRing k n i) :=
    coordinateChartRing_isIntegrallyClosed k n i
  exact spec_isNormalScheme_of_isIntegrallyClosed (coordinateChartRing k n i)

/-- Every standard open restriction is normal via its actual `Proj`
isomorphism to the affine chart. -/
theorem coordinateStandardOpen_isNormalScheme (i : Fin (n + 1)) :
    IsNormalScheme
      (Proj.basicOpen (grading k n) (MvPolynomial.X i)).toScheme :=
  isNormalScheme_of_isOpenImmersion
    (Proj.basicOpenIsoSpec (grading k n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) (by decide)).hom
    (coordinateChartSpec_isNormalScheme k n i)

/-- A polynomial in the irrelevant ideal has zero constant coefficient.
Every supported monomial therefore contains a variable, so the variables
span the irrelevant ideal. -/
theorem irrelevant_le_span_coordinates :
    (HomogeneousIdeal.irrelevant (grading k n)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → homogeneousRing k n)) := by
  classical
  intro p hp
  have hproj : GradedRing.proj (grading k n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at hproj
  change (MvPolynomial.decomposition.decompose' p 0 : homogeneousRing k n) = 0 at hproj
  rw [MvPolynomial.decomposition.decompose'_apply] at hproj
  rw [MvPolynomial.homogeneousComponent_zero] at hproj
  have hzero : MvPolynomial.coeff 0 p = 0 := by
    apply MvPolynomial.C_injective (Fin (n + 1)) k
    simpa only [map_zero] using hproj
  rw [← Set.image_univ (f := (MvPolynomial.X : Fin (n + 1) → homogeneousRing k n)),
    MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hmzero : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.mp hm) hzero
  by_contra! h
  apply hmzero
  ext i
  simpa using h i

/-- The actual coordinate basic opens cover projective space. -/
theorem iSup_coordinateStandardOpen :
    ⨆ i : Fin (n + 1), Proj.basicOpen (grading k n) (MvPolynomial.X i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (grading k n) MvPolynomial.X
    (irrelevant_le_span_coordinates k n)

/-- The usual finite standard affine cover, built from the actual `Proj`
chart immersions and the proved spanning statement. -/
def standardAffineCover : (projectiveSpace k n).AffineOpenCover :=
  Proj.openCoverOfISupEqTop (grading k n)
    (MvPolynomial.X : Fin (n + 1) → homogeneousRing k n)
    (m := fun _ ↦ 1) (fun i ↦ MvPolynomial.isHomogeneous_X k i)
    (fun _ ↦ Nat.zero_lt_one) (irrelevant_le_span_coordinates k n)

end ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual projective space over a field is normal. The finite coordinate
cover places every point in a normal affine chart, whose open immersion
identifies the corresponding structure-sheaf stalks. -/
theorem projectiveSpace_isNormalScheme (k : Type u) [Field k] (n : ℕ) :
    IsNormalScheme (projectiveSpace k n) := by
  intro x
  let i : Fin (n + 1) := (ProjectiveChart.standardAffineCover k n).f x
  have hx : x ∈ Proj.basicOpen (ProjectiveChart.grading k n) (MvPolynomial.X i) := by
    have hc := (ProjectiveChart.standardAffineCover k n).covers x
    change x ∈ (Proj.awayι (ProjectiveChart.grading k n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) (by decide)).opensRange at hc
    rwa [Proj.opensRange_awayι] at hc
  exact normal_stalk_at_image_of_isOpenImmersion
    (Proj.basicOpen (ProjectiveChart.grading k n) (MvPolynomial.X i)).ι
    (ProjectiveChart.coordinateStandardOpen_isNormalScheme k n i) ⟨x, hx⟩

end KltDP.Geometry
