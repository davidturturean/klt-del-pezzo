import KltDP.Geometry.AffineBlowupBoundaryRadicals

/-!
# Actual branch supports off the centre in an original Rees chart

The original chart inclusion followed by the original blowup projection
has the prescribed base-ring map. The denominator branch has empty inverse
image off the centre. The other branch has exactly the vanishing locus of
the original Rees fraction away from the original exceptional equation.
This identifies the set whose closure gives the strict-transform support;
density of that punctured residual component is a separate geometric step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineBlowup

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/-- Zero loci pull back under the actual chart projection by the actual ring map. -/
theorem chart_projection_preimage_zeroLocus (s : Set R) :
    (chartι I a ≫ toSpec I).base ⁻¹' PrimeSpectrum.zeroLocus s =
      PrimeSpectrum.zeroLocus ((chartBaseMap I a) '' s) := by
  rw [chartι_toSpec]
  exact PrimeSpectrum.preimage_comap_zeroLocus (chartBaseMap I a) s

/-- The actual inverse image of the centre is the original exceptional chart equation. -/
theorem chart_projection_preimage_center :
    (chartι I a ≫ toSpec I).base ⁻¹' PrimeSpectrum.zeroLocus (I : Set R) =
      PrimeSpectrum.zeroLocus {chartBaseMap I a (a : R)} := by
  rw [chart_projection_preimage_zeroLocus]
  calc
    _ = PrimeSpectrum.zeroLocus
        (Ideal.span ((chartBaseMap I a) '' (I : Set R)) : Set (chartRing I a)) :=
      (PrimeSpectrum.zeroLocus_span _).symm
    _ = _ := by
      change PrimeSpectrum.zeroLocus (Ideal.map (chartBaseMap I a) I : Set (chartRing I a)) = _
      rw [map_chartBaseMap_ideal, PrimeSpectrum.zeroLocus_span]

/-- The denominator branch contributes no points off the centre in this original chart. -/
theorem chart_first_branch_off_center_empty :
    (chartι I a ≫ toSpec I).base ⁻¹'
      (PrimeSpectrum.zeroLocus ({(a : R)} : Set R) \ PrimeSpectrum.zeroLocus (I : Set R)) = ∅ := by
  rw [Set.preimage_diff, chart_projection_preimage_zeroLocus, Set.image_singleton,
    chart_projection_preimage_center, Set.diff_self]

/-- The other branch off the centre is the literal residual-fraction zero
locus away from the actual exceptional equation. -/
theorem chart_second_branch_off_center :
    (chartι I a ≫ toSpec I).base ⁻¹'
      (PrimeSpectrum.zeroLocus ({(b : R)} : Set R) \ PrimeSpectrum.zeroLocus (I : Set R)) =
      PrimeSpectrum.zeroLocus {chartFraction I a b} \
        PrimeSpectrum.zeroLocus {chartBaseMap I a (a : R)} := by
  rw [Set.preimage_diff, chart_projection_preimage_zeroLocus, Set.image_singleton,
    chart_projection_preimage_center, ← chartBaseMap_mul_chartFraction I a b,
    PrimeSpectrum.zeroLocus_singleton_mul]
  ext z
  constructor
  · rintro ⟨h | h, hn⟩
    · exact (hn h).elim
    · exact ⟨h, hn⟩
  · rintro ⟨h, hn⟩
    exact ⟨Or.inr h, hn⟩

/-- Its conventional chartwise strict-support closure is the closure of
the punctured original residual component, without a supplied closure identity. -/
theorem chart_second_branch_closure :
    closure ((chartι I a ≫ toSpec I).base ⁻¹'
      (PrimeSpectrum.zeroLocus ({(b : R)} : Set R) \ PrimeSpectrum.zeroLocus (I : Set R))) =
      closure (PrimeSpectrum.zeroLocus {chartFraction I a b} \
        PrimeSpectrum.zeroLocus {chartBaseMap I a (a : R)}) := by
  rw [chart_second_branch_off_center]

end KltDP.Geometry.AffineBlowup
