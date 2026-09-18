import KltDP.Geometry.PushforwardRelativeSpecSurjectivity
import KltDP.Geometry.PushforwardRelativeSpecStructureSheaf
import KltDP.Geometry.PushforwardNormalizationConstruction
import KltDP.Geometry.SteinTargetIntegral

/-!
Integrality and normality of the actual pushforward relative spectrum.
The original proper source map supplies surjectivity and its canonical
structure-sheaf isomorphism by the proved producers. No target property
or theorem-shaped compatibility premise is assumed. The separately
constructed integral-closure target inherits the same properties through
the actual canonical comparison, preserving both original target objects.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- An integral proper source gives an integral actual relative-spectrum target. -/
theorem relativeSpec_isIntegral [IsIntegral X] : IsIntegral (relativeSpec f) := by
  letI : IsIso (fromSource f).c := fromSource_c_isIso f
  exact SteinTargetIntegral.integral (fromSource f) (fromSource_surjective f).surj

/-- A normal integral proper source gives a normal actual relative-spectrum target. -/
theorem relativeSpec_isNormal [IsIntegral X] (hnormal : IsNormalScheme X) :
    IsNormalScheme (relativeSpec f) := by
  letI : IsIso (fromSource f).c := fromSource_c_isIso f
  exact (SteinTargetIntegral.integral_and_normal (fromSource f) hnormal
    (fromSource_surjective f).surj).2

/-- The separately constructed integral-closure gluing is integral as well. -/
theorem normalization_isIntegral [IsIntegral X] : IsIntegral (normalization f) := by
  letI : IsIntegral (relativeSpec f) := relativeSpec_isIntegral f
  letI : Nonempty (normalization f) :=
    Nonempty.map (normalizationComparison f).hom.base inferInstance
  exact isIntegral_of_isOpenImmersion (normalizationComparison f).inv

/-- The original integral-closure target is normal, using the actual canonical comparison. -/
theorem normalization_isNormal [IsIntegral X] (hnormal : IsNormalScheme X) :
    IsNormalScheme (normalization f) :=
  isNormalScheme_of_isOpenImmersion (normalizationComparison f).inv
    (relativeSpec_isNormal f hnormal)

end KltDP.Geometry.PushforwardRelativeSpec
