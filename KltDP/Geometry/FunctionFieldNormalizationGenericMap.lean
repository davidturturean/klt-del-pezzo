import KltDP.Geometry.NormalSchemeAffineNormalization
import Mathlib.AlgebraicGeometry.Stalk

/-!
# The original generic-point map through the actual normalization charts

The map from the spectrum of the original function field is induced by
the literal integral-closure inclusion.  Its composite is the canonical
map from the original generic stalk, as used to define absolute
normalization.  No field identification or generic map is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalSchemeAffineNormalization

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual integral-closure inclusion gives the original generic chart map. -/
def genericToChart (U : X.Opens) [Nonempty U] :
    Spec X.functionField ⟶ chart X U :=
  Spec.map (CommRingCat.ofHom
    (integralClosure Γ(X, U) X.functionField).val.toRingHom)

/-- Its composite is the spectrum map of the unchanged generic germ. -/
@[reassoc] theorem genericToChart_projection (U : X.Opens) [Nonempty U] :
    genericToChart X U ≫ projection X U = Spec.map (X.germToFunctionField U) := by
  unfold genericToChart projection
  rw [← Spec.map_comp]
  congr 1

/-- Every actual affine chart gives the same canonical morphism from the
spectrum of the original generic stalk. -/
@[reassoc] theorem genericToChart_to_original (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    genericToChart X U ≫ projection X U ≫ hU.fromSpec =
      X.fromSpecStalk (genericPoint X) := by
  rw [genericToChart_projection_assoc]
  exact hU.fromSpecStalk_eq_fromSpecStalk _

end KltDP.Geometry.NormalSchemeAffineNormalization

#print axioms KltDP.Geometry.NormalSchemeAffineNormalization.genericToChart_to_original
