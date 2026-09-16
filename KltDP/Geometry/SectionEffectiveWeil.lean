import KltDP.Geometry.SectionEffectiveCartier
import KltDP.Geometry.DivisorOrderLength
import KltDP.Geometry.RegularSurfaceWeilPicard

/-!
# Effective integral Weil representatives from original nonzero sections

A regular Cartier equation has a nonzero germ at every point of its chart:
its image in the original function field is the original rational equation.
At a DVR stalk, the existing quotient-length formula makes its order
nonnegative. Applied at each original prime curve, this proves effectivity
of the already constructed finite Cartier-to-Weil divisor.

For an original nonzero section of O(D), the existing principal shift uses
that section's own rational value q and produces regular equations for
D + div(q). The original Cartier-to-Weil homomorphism keeps the same q, so
the resulting finite effective Weil divisor is linearly equivalent to the
original divisor under the existing principal-divisor relation.

The final specialization uses the existing Cartier representative of an
original Weil divisor on a regular surface. Its algebraically closed base
is inherited from that representation API. No Euler bound, Riemann--Roch,
vanishing, nonempty zero locus, or numerical intersection is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

section Scheme

variable (X : Scheme.{u}) [IsIntegral X]

local instance (x : X) : IsDomain (X.presheaf.stalk x) :=
  integralSchemeStalk_isDomain X x

/-- A regular equation has nonnegative order at an original DVR stalk
lying in its chart, via the original germ and fraction-field maps. -/
theorem RegularCartierEquationChart.stalkOrder_nonneg
    (D : CartierDivisor X) (c : RegularCartierEquationChart X D)
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hx : x ∈ c.chart.openSet) :
    0 ≤ stalkDivisorOrder X x c.chart.equation := by
  let r : X.presheaf.stalk x :=
    (X.presheaf.germ c.chart.openSet x hx).hom c.coefficient
  have hmap : algebraMap (X.presheaf.stalk x) X.functionField r =
      (c.chart.equation : X.functionField) := by
    change (X.presheaf.stalkSpecializes
        ((genericPoint_spec X).specializes trivial))
        ((X.presheaf.germ c.chart.openSet x hx) c.coefficient) = _
    exact (ConcreteCategory.congr_hom
      (X.presheaf.germ_stalkSpecializes hx
        ((genericPoint_spec X).specializes trivial)) c.coefficient).trans c.germ_eq
  have hr : r ≠ 0 := by
    intro hz
    have h := hmap
    rw [hz, map_zero] at h
    exact (Units.ne_zero c.chart.equation) h.symm
  have hunit :
      RingTheory.fractionFieldUnit (X.presheaf.stalk x) X.functionField r hr =
        c.chart.equation := by
    apply Units.ext
    exact hmap
  rw [← hunit]
  exact RingTheory.divisorOrder_algebraMap_nonneg
    (X.presheaf.stalk x) X.functionField r hr

end Scheme

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Regular Cartier equations give nonnegative coefficients in the
original finite Weil divisor, using the proved prime-curve DVR stalks. -/
theorem effective_cartierToWeilHom_of_regularEquations
    (E : CartierDivisor X.toScheme)
    (hE : HasRegularCartierEquations X.toScheme E) :
    EffectiveDivisor (X.cartierToWeilHom E) := by
  intro C
  letI : IsDiscreteValuationRing (X.stalk C.genericPoint) :=
    C.genericPoint_isDiscreteValuationRing
  obtain ⟨c, hc⟩ := hE C.genericPoint
  rw [X.cartierToWeilHom_apply_of_equation E C c.chart.openSet hc
    c.chart.equation c.chart.represents]
  exact RegularCartierEquationChart.stalkOrder_nonneg
    X.toScheme E c C.genericPoint hc

/-- The actual rational value of an original nonzero section supplies
the principal difference from a finite effective integral Weil divisor. -/
theorem exists_effectiveWeil_of_nonzero_cartier_section
    (D : CartierDivisor X.toScheme)
    (s : (cartierDivisorModule X.toScheme D).val.obj (op (⊤ : X.toScheme.Opens)))
    (hs : s ≠ 0) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧
      X.LinearlyEquivalent Z (X.cartierToWeilHom D) := by
  let q : X.toScheme.functionFieldˣ :=
    Units.mk0 (cartierGlobalSectionRationalValue X.toScheme D s)
      (cartierGlobalSectionRationalValue_ne_zero X.toScheme D s hs)
  let E := D + principalCartierDivisorHom X.toScheme (Additive.ofMul q)
  have hE : HasRegularCartierEquations X.toScheme E :=
    cartierPrincipalShift_hasRegularEquations X.toScheme D s q rfl
  refine ⟨X.cartierToWeilHom E,
    X.effective_cartierToWeilHom_of_regularEquations E hE, q, ?_⟩
  change X.cartierToWeilHom
      (D + principalCartierDivisorHom X.toScheme (Additive.ofMul q)) -
        X.cartierToWeilHom D = X.principalDivisor q
  rw [map_add, X.cartierToWeilHom_principal]
  abel

section Regular

variable [IsAlgClosed k]
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- For the existing actual O(D) realization of an original Weil divisor,
a genuine nonzero section gives an effective integral representative in
its original linear-equivalence class. Finite support is part of the
existing Weil-divisor type. -/
theorem exists_effectiveWeil_of_nonzero_section
    (D : X.WeilDivisor)
    (s : (cartierDivisorModule X.toScheme
      ((X.regularCartierWeilEquiv hregular).symm D)).val.obj
        (op (⊤ : X.toScheme.Opens))) (hs : s ≠ 0) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧ X.LinearlyEquivalent Z D := by
  have hD : X.cartierToWeilHom ((X.regularCartierWeilEquiv hregular).symm D) = D :=
    (X.regularCartierWeilEquiv hregular).apply_symm_apply D
  obtain ⟨Z, hZ, hZD⟩ := X.exists_effectiveWeil_of_nonzero_cartier_section
    ((X.regularCartierWeilEquiv hregular).symm D) s hs
  exact ⟨Z, hZ, by simpa only [hD] using hZD⟩

end Regular

end NormalProjectiveSurface
end KltDP.Geometry
