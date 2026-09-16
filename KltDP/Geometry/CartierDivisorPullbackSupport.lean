import KltDP.Geometry.CartierDivisorPullback
import KltDP.Geometry.PrimeCurveCartierRestriction

/-!
# The support of a pulled-back Cartier divisor (BRIEF38)

`Supp(π^*D) = π⁻¹(Supp D)` for an effective Cartier divisor `D` with regular equations on `Y` and a
generic-point-preserving morphism `π : X ⟶ Y` of integral schemes.

Nothing in the accepted tree related the support of a *pulled-back* divisor to the support downstairs:
the only support-transport results are for **kernel** ideals under open base change
(`support_ker_openBaseChange`), which do not apply to `effectiveCartierIdealDataOfRegularEquations` of
a `pullbackDivisor`. This module supplies the missing statement, in `KltDP.Geometry` so that every lane
can consume it.

The proof is the accepted `mem_support_restrictCartier_iff` with the closed immersion of a curve
replaced by `π`. Both sides are read off by the accepted **`mem_support_iff_not_isUnit_germ`**, which is
stated for an arbitrary integral scheme, so it applies upstairs and downstairs alike:

* a chart of `D` at `π.base z` gives a chart of `π^*D` at `z` (`pullbackDivisor_regularChart`), whose
  open is `π ⁻¹ᵁ c.chart.openSet` and whose coefficient is `π.app _ c.coefficient`, both by `rfl`;
* `Scheme.stalkMap_germ_apply` identifies the germ upstairs with `π.stalkMap z` of the germ downstairs;
* `π.stalkMap z` is a **local** homomorphism, so it both preserves and reflects units
  (`isUnit_map_iff`) — which is why the equality comes out whole rather than only the inclusion `⊆`.

* **`mem_support_pullbackDivisor_iff`** — the pointwise criterion;
* **`support_pullbackDivisor_eq_preimage`** — the sets are equal;
* `support_pullbackDivisor_subset` — the inclusion alone, for consumers that only need that direction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

-- `mem_support_iff_not_isUnit_germ` is stated for an arbitrary integral scheme but lives under the
-- surface/curve namespace `KltDP.Geometry.NormalProjectiveSurface.PrimeCurve`, so it must be opened
-- explicitly even from inside `KltDP.Geometry`. (A docstring cannot precede `open`: it is a command,
-- not a declaration.)
open NormalProjectiveSurface.PrimeCurve

section PullbackSupport

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [GenericPointPreserving π]
  (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)

/-- **A point lies in the support of `π^*D` exactly when its image lies in the support of `D`.**
The stalk map of `π` is local, so it reflects units as well as preserving them. -/
theorem mem_support_pullbackDivisor_iff (z : X) :
    z ∈ (effectiveCartierIdealDataOfRegularEquations X (pullbackDivisor π D hD)
        (pullbackDivisor_hasRegularEquations π D hD)).support ↔
      π.base z ∈ (effectiveCartierIdealDataOfRegularEquations Y D hD).support := by
  obtain ⟨c, hc⟩ := hD (π.base z)
  rw [mem_support_iff_not_isUnit_germ (pullbackDivisor π D hD)
      (pullbackDivisor_hasRegularEquations π D hD) (pullbackDivisor_regularChart π D hD c) z hc,
    mem_support_iff_not_isUnit_germ D hD c (π.base z) hc]
  have hgerm := Scheme.stalkMap_germ_apply π c.chart.openSet z hc c.coefficient
  change ¬ IsUnit (X.presheaf.germ (π ⁻¹ᵁ c.chart.openSet) z hc
    (pulledCoefficient π D c)) ↔ _
  rw [pulledCoefficient, ← hgerm]
  exact not_congr (isUnit_map_iff (π.stalkMap z).hom _)

/-- **The support of the pullback is the preimage of the support.** -/
theorem support_pullbackDivisor_eq_preimage :
    ((effectiveCartierIdealDataOfRegularEquations X (pullbackDivisor π D hD)
        (pullbackDivisor_hasRegularEquations π D hD)).support : Set X) =
      π.base ⁻¹' ((effectiveCartierIdealDataOfRegularEquations Y D hD).support : Set Y) :=
  Set.ext fun z => mem_support_pullbackDivisor_iff π D hD z

/-- The inclusion alone, for consumers that need only this direction. -/
theorem support_pullbackDivisor_subset :
    ((effectiveCartierIdealDataOfRegularEquations X (pullbackDivisor π D hD)
        (pullbackDivisor_hasRegularEquations π D hD)).support : Set X) ⊆
      π.base ⁻¹' ((effectiveCartierIdealDataOfRegularEquations Y D hD).support : Set Y) :=
  (support_pullbackDivisor_eq_preimage π D hD).subset

/-- Contrapositive form: off the support downstairs, the preimage point is off the support
upstairs — the shape a `NotInSupport` argument consumes. -/
theorem not_mem_support_pullbackDivisor (z : X)
    (hz : π.base z ∉ (effectiveCartierIdealDataOfRegularEquations Y D hD).support) :
    z ∉ (effectiveCartierIdealDataOfRegularEquations X (pullbackDivisor π D hD)
      (pullbackDivisor_hasRegularEquations π D hD)).support :=
  fun h => hz ((mem_support_pullbackDivisor_iff π D hD z).mp h)

end PullbackSupport

end KltDP.Geometry
