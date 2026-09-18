import KltDP.Geometry.RegularSurfaceBlowupReducedIdeals
import KltDP.Geometry.SchematicImageOpenBaseChange
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Original reduced boundary ideal sheaves on the actual Rees chart

The actual quotient by the residual fraction defines the ideal sheaf of
the original strict-support closure. The actual quotient by exceptional
times fraction defines the ideal sheaf of the reduced exceptional plus
original two-branch pullback. Reducedness follows from the proved original
radical ideals, so the existing reduced-source kernel theorem supplies
scheme ideal-sheaf equalities, beyond the earlier equalities of ring ideals.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup

private theorem reducedQuotient_ker {S : Type u} [CommRing S]
    (J : Ideal S) (hJ : J.IsRadical) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker =
      Scheme.IdealSheafData.vanishingIdeal (X := Spec (CommRingCat.of S))
        ⟨PrimeSpectrum.zeroLocus (J : Set S), PrimeSpectrum.isClosed_zeroLocus _⟩ := by
  letI : _root_.IsReduced (S ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).mp hJ
  apply (SchematicImageOpenBaseChange.ker_eq_vanishingIdeal_rangeClosure
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).trans
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply Closeds.ext
  change closure (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))) =
    PrimeSpectrum.zeroLocus (J : Set S)
  rw [PrimeSpectrum.closure_range_comap, Ideal.mk_ker]

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (I : Ideal R) (a b : I)
variable (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
variable (hI : I = Ideal.span {(a : R), (b : R)}) (hmax : I = maximalIdeal R)

include hR hdim hI hmax in
/-- The kernel of the original residual quotient is the actual ideal sheaf
of the strict-support closure of the given original second branch. -/
theorem residual_branch_idealSheaf :
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {chartFraction I a b})))).ker =
      Scheme.IdealSheafData.vanishingIdeal (X := Spec (CommRingCat.of (chartRing I a)))
        ⟨closure ((chartι I a ≫ toSpec I).base ⁻¹'
          (PrimeSpectrum.zeroLocus {(b : R)} \ PrimeSpectrum.zeroLocus (I : Set R))),
          isClosed_closure⟩ := by
  apply (reducedQuotient_ker (Ideal.span {chartFraction I a b})
    (fraction_ideal_isPrime_of_surface_parameters I a b hR hdim hI hmax).isRadical).trans
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply Closeds.ext
  change PrimeSpectrum.zeroLocus (Ideal.span {chartFraction I a b} : Set (chartRing I a)) =
    closure ((chartι I a ≫ toSpec I).base ⁻¹'
      (PrimeSpectrum.zeroLocus {(b : R)} \ PrimeSpectrum.zeroLocus (I : Set R)))
  rw [PrimeSpectrum.zeroLocus_span,
    original_parameter_branch_closure I a b hR hdim hI hmax]

include hR hdim hI hmax in
/-- The original exceptional-times-fraction quotient has exactly the
reduced ideal sheaf of the exceptional plus original two-branch pullback. -/
theorem reduced_exceptional_pair_idealSheaf :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b})))).ker =
      Scheme.IdealSheafData.vanishingIdeal (X := Spec (CommRingCat.of (chartRing I a)))
        ⟨PrimeSpectrum.zeroLocus ((chartCenterIdeal I a *
          Ideal.map (chartBaseMap I a) (Ideal.span {(a : R) * (b : R)})) :
          Set (chartRing I a)), PrimeSpectrum.isClosed_zeroLocus _⟩ := by
  have hrad : (Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b}).IsRadical :=
    Ideal.radical_eq_iff.mp (exceptional_fraction_span_radical I a b hR hdim hI hmax)
  apply (reducedQuotient_ker
    (Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b}) hrad).trans
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply Closeds.ext
  change PrimeSpectrum.zeroLocus
      (Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b} : Set (chartRing I a)) =
    PrimeSpectrum.zeroLocus ((chartCenterIdeal I a *
      Ideal.map (chartBaseMap I a) (Ideal.span {(a : R) * (b : R)})) : Set (chartRing I a))
  rw [← reduced_exceptional_pair_ideal I a b hR hdim hI hmax, PrimeSpectrum.zeroLocus_radical]

end KltDP.Geometry.AffineBlowupRegularPairChart
