import KltDP.Geometry.PushforwardRelativeSpecConstruction

/-!
# Actual source charts of the canonical relative-spectrum map

The original source open is the pullback of its original target chart.
This follows by cancelling the already-proved right cartesian square
from the original restriction square; no source-chart compatibility
is introduced as an assumption.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Limits
universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

open PushforwardAffinizationCharts
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The original open affinization is the actual restriction of the global source map. -/
theorem fromSource_chart_isPullback (U : Y.AffineZariskiSite) :
    IsPullback (f ⁻¹ᵁ U.1).toSpecΓ (f ⁻¹ᵁ U.1).ι (chart f U) (fromSource f) := by
  have ha : (f ⁻¹ᵁ U.1).toSpecΓ ≫ (Spec.map (f.app U.1) ≫ U.2.isoSpec.inv) =
      f ∣_ U.1 := by
    rw [toSpecΓ_SpecMap_app_assoc, IsAffineOpen.toSpecΓ_isoSpec_inv, Category.comp_id]
  refine IsPullback.of_right (h₁₂ := Spec.map (f.app U.1) ≫ U.2.isoSpec.inv)
    (h₂₂ := toBase f) ?_ (source_ι_fromSource f U).symm (chart_isPullback f U)
  rw [ha, fromSource_toBase]
  exact isPullback_morphismRestrict f U.1

end KltDP.Geometry.PushforwardRelativeSpec
