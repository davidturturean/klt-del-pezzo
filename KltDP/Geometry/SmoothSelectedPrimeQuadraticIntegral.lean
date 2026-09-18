import KltDP.Geometry.OriginalCartierQuadraticIntegral
import KltDP.Geometry.SmoothSurfaceDivisorPicard

/-!
# An integral original cover from a nonempty even curve selection

Actual smoothness of the original surface supplies the factorial stalks
used by the existing Cartier/Weil construction. The original finite
curve selection and its integral Picard half-class then supply the
Cartier divisor, its canonical section, its half-line, and its actual
reduced zero scheme. Nonempty selection proves nonemptiness of that same
zero scheme. The cover is therefore integral, finite, and flat.

The original branch ideal is identified with the reduced selected union.
No original curve is replaced and no cover-integrality, local coordinate,
valuation, branch quotient, or independent geometric cover is an input.
Branch smoothness is unnecessary for this integrality conclusion.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance smoothSelectedPrimeQuadraticIntegralSeparated : S.toScheme.IsSeparated := surfaceSeparated S

local instance smoothSelectedPrimeQuadraticIntegralMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- A nonempty even selection on the actual smooth surface produces its original integral cover. -/
theorem exists_integral_quadratic_cover_of_nonempty_even_selection
    (N : Finset S.PrimeCurve) (hN : N.Nonempty) (m : Additive S.toScheme.Pic)
    (heven : S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) =
      (2 : ℕ) • m) :
    ∃ (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
      (L : InvertibleSheaf S.toScheme)
      (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E),
      S.cartierToWeilHom E = S.selectedPrimeWeil N ∧ L.toPic = m.toMul ∧
      effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
        Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N) ∧
      let A := InvertibleQuadraticAtlas.fromSquareRoot S.toScheme L
        (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)
      IsIntegral A.scheme ∧ IsFinite A.morphism ∧ AlgebraicGeometry.Flat A.morphism := by
  letI : ∀ x : S.toScheme, UniqueFactorizationMonoid (S.stalk x) :=
    S.stalks_uniqueFactorizationMonoid_of_regular S.regularPoints_of_isSmooth
  have heven' : S.weilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) =
      (2 : ℕ) • m := heven
  obtain ⟨L, e, hL, hIJ, hred, hrange, _hiso⟩ :=
    S.selectedPrimeCurve_reducedUnion_of_even_picard N m heven'
  let E := S.selectedPrimeCartier N
  let hE := S.hasRegularCartierEquations_of_effective_weil E (S.selectedPrimeCartier_effective N)
  have hred' : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued := by
    rw [← effectiveCartierIdealData_eq_ofRegularEquations S.toScheme E hE L e]
    exact hred
  have hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued := by
    rw [← effectiveCartierIdealData_eq_ofRegularEquations S.toScheme E hE L e]
    obtain ⟨x, hx⟩ := S.selectedPrimeClosedUnion_nonempty N hN
    have hx' : x ∈ Set.range (effectiveCartierIdealData S.toScheme E hE L e).gluedTo.base := by
      rw [hrange]
      exact hx
    obtain ⟨y, _hy⟩ := hx'
    exact ⟨y⟩
  have hIJ' : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N) :=
    (effectiveCartierIdealData_eq_ofRegularEquations S.toScheme E hE L e).symm.trans hIJ
  have hint := OriginalCartierQuadraticIntegral.scheme_isIntegral_of_reduced_nonempty_branch
    S.toScheme E hE L e S.normal hred' hne
  have hfin := InvertibleQuadraticAtlas.fromSquareRoot_finite_flat S.toScheme L
    (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)
  exact ⟨E, hE, L, e, S.selectedPrimeCartier_weil N, hL, hIJ', hint, hfin.1, hfin.2⟩

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_integral_quadratic_cover_of_nonempty_even_selection
