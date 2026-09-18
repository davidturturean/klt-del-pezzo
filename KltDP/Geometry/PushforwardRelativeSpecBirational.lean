import KltDP.Geometry.PushforwardRelativeSpecNormalTarget
import KltDP.Geometry.BirationalComposition
import KltDP.Geometry.DominantGenericPoint

/-!
The original relative-spectrum factorization of a proper birational map
is birational in both factors. Integrality of its actual target and
surjectivity of its actual source map are derived. The exact original
triangle then supplies generic-point preservation of the base map and
allows the compiled function-field composition criterion to apply.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f]

/-- Both actual maps in the constructed factorization are birational. -/
theorem fromSource_and_toBase_isBirational (hf : IsBirationalScheme f) :
    letI : IsIntegral (relativeSpec f) := relativeSpec_isIntegral f
    IsBirationalScheme (fromSource f) ∧ IsBirationalScheme (toBase f) := by
  letI : IsIntegral (relativeSpec f) := relativeSpec_isIntegral f
  letI : Surjective (fromSource f) := fromSource_surjective f
  letI : GenericPointPreserving (fromSource f) :=
    genericPointPreserving_of_isDominant (fromSource f)
  letI : GenericPointPreserving (toBase f) := by
    constructor
    have h := congrArg (fun a : X ⟶ Y => a.base (genericPoint X))
      (fromSource_toBase f)
    change (toBase f).base ((fromSource f).base (genericPoint X)) =
      f.base (genericPoint X) at h
    rw [GenericPointPreserving.base_genericPoint (π := fromSource f),
      hf.map_genericPoint] at h
    exact h
  apply BirationalComposition.isBirationalScheme_factors_of_comp
    (fromSource f) (toBase f)
  rwa [fromSource_toBase]

end KltDP.Geometry.PushforwardRelativeSpec
