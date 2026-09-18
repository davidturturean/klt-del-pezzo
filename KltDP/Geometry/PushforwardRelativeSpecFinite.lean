import KltDP.Geometry.PushforwardRelativeSpecConstruction
import KltDP.Geometry.ProperPushforwardAffineFiniteness

/-!
# Finiteness and properness of the actual relative-spectrum factorization

The original affine base cover and the constructed cartesian chart
squares identify each actual base change of `toBase f` with the finite
original chart map. Target locality gives global finiteness. The exact
original factorization then makes `fromSource f` proper, since the finite
base map is separated. No factorization or chart property is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

open Scheme.AffineZariskiSite

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f]

/-- The constructed global map from the actual relative spectrum to its base is finite. -/
theorem toBase_isFinite : IsFinite (toBase f) := by
  apply IsLocalAtTarget.of_openCover (P := @IsFinite) (directedCover Y)
  intro U
  change IsFinite (pullback.snd (toBase f) U.1.ι)
  letI : IsFinite (Spec.map (f.app U.1) ≫ U.2.isoSpec.inv) :=
    ProperPushforwardAffineFiniteness.datum_natTrans_isFinite f U
  rw [← (chart_isPullback f U).flip.isoPullback_inv_snd]
  infer_instance

/-- The constructed canonical map from the original proper source is proper. -/
theorem fromSource_isProper : IsProper (fromSource f) := by
  letI : IsFinite (toBase f) := toBase_isFinite f
  letI : IsProper (fromSource f ≫ toBase f) := by
    rw [fromSource_toBase]
    infer_instance
  exact IsProper.of_comp_of_isSeparated (fromSource f) (toBase f)

end KltDP.Geometry.PushforwardRelativeSpec
