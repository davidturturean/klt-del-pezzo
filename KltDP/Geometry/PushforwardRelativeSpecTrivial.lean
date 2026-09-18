import KltDP.Geometry.PushforwardRelativeSpecConstruction
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
The actual relative-spectrum base map is an isomorphism whenever the
original canonical pushforward structure-sheaf map is an isomorphism.
The original affine chart squares and target locality supply the result;
there is no properness, Noetherianity, integrality or normality premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

open Scheme.AffineZariskiSite

/-- The original structure-sheaf isomorphism trivializes the actual
relative spectrum over its original base. -/
theorem toBase_isIso_of_c_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsIso f.c] : IsIso (toBase f) := by
  apply IsLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    (directedCover Y)
  intro U
  change IsIso (pullback.snd (toBase f) U.1.ι)
  letI : IsIso (f.app U.1) := show IsIso (f.c.app (op U.1)) from inferInstance
  letI : IsIso (Spec.map (f.app U.1) ≫ U.2.isoSpec.inv) := inferInstance
  rw [← (chart_isPullback f U).flip.isoPullback_inv_snd]
  infer_instance

end KltDP.Geometry.PushforwardRelativeSpec
