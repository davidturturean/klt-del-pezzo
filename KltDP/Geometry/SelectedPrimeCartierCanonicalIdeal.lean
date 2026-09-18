import KltDP.Geometry.SelectedPrimeCurveCartierUnion
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal

/-!
# The canonical ideal of the actual selected Cartier divisor

The existing germ criterion and radicality theorem identify the
canonical regular-equation ideal directly, without a square-root line
bundle. Applied to the actual selected Cartier divisor, its canonical
ideal is the vanishing ideal of exactly the selected prime-curve union.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]

/-- The canonical regular-equation ideal has the actual Cartier-to-Weil support. -/
theorem canonicalCartierIdeal_support (E : CartierDivisor X.toScheme)
    (hE : HasRegularCartierEquations X.toScheme E) :
    ((effectiveCartierIdealDataOfRegularEquations X.toScheme E hE).support :
      Set X.toScheme) = divisorSupport (X.cartierToWeilHom E) := by
  classical
  ext x
  obtain ⟨c, hxc⟩ := hE x
  simp only [SetLike.mem_coe]
  rw [PrimeCurve.mem_support_iff_not_isUnit_germ E hE c x hxc,
    X.regularCartierEquation_germ_isUnit_iff E c ⟨x, hxc⟩, mem_divisorSupport]
  constructor
  · intro h
    by_contra hn
    apply h
    intro C hxC
    by_contra hC
    exact hn ⟨C, hC, hxC⟩
  · rintro ⟨C, hC, hxC⟩ hz
    exact hC (hz C hxC)

/-- Coefficients at most one identify the canonical ideal with the reduced support ideal. -/
theorem canonicalCartierIdeal_eq_vanishingIdeal (E : CartierDivisor X.toScheme)
    (hE : HasRegularCartierEquations X.toScheme E)
    (heff : EffectiveDivisor (X.cartierToWeilHom E))
    (hone : ∀ C, X.cartierToWeilHom E C ≤ 1) :
    effectiveCartierIdealDataOfRegularEquations X.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨divisorSupport (X.cartierToWeilHom E), divisorSupport_isClosed _⟩ := by
  let I := effectiveCartierIdealDataOfRegularEquations X.toScheme E hE
  have hrad : I.radical = I := by
    ext U : 2
    change (I.ideal U).radical = I.ideal U
    apply Ideal.radical_eq_iff.mpr
    rw [show I.ideal U = cartierSectionIdeal X.toScheme E U.1 from
      effectiveCartierIdealDataOfRegularEquations_ideal X.toScheme E hE U]
    exact X.cartierSectionIdeal_isRadical E heff hone U.1
  calc
    I = I.radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal I.support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = _ := congrArg Scheme.IdealSheafData.vanishingIdeal
      (Closeds.ext (X.canonicalCartierIdeal_support E hE))

/-- The actual selected Cartier divisor has exactly the actual selected reduced union ideal. -/
theorem selectedPrimeCartier_canonicalIdeal (N : Finset X.PrimeCurve) :
    effectiveCartierIdealDataOfRegularEquations X.toScheme (X.selectedPrimeCartier N)
      (X.hasRegularCartierEquations_of_effective_weil _ (X.selectedPrimeCartier_effective N)) =
        Scheme.IdealSheafData.vanishingIdeal (X.selectedPrimeClosedUnion N) := by
  rw [X.canonicalCartierIdeal_eq_vanishingIdeal _ _
    (X.selectedPrimeCartier_effective N) (X.selectedPrimeCartier_le_one N)]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply Closeds.ext
  change divisorSupport (X.cartierToWeilHom (X.selectedPrimeCartier N)) =
    (X.selectedPrimeClosedUnion N : Set X.toScheme)
  rw [X.selectedPrimeCartier_weil, X.selectedPrimeWeil_divisorSupport]

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.canonicalCartierIdeal_support
#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedPrimeCartier_canonicalIdeal

