import KltDP.Geometry.PushforwardSourceCover
import KltDP.Geometry.PushforwardAffineDiagram

/-!
# Original chart affinization maps

The actual inverse-image open maps to the spectrum of its original
section ring by the pinned `Scheme.Opens.toSpecΓ`. Its transition
compatibility is exactly the pinned original restriction naturality
theorem. No affine, proper, or qcqs premise is needed for this map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Geometry.PushforwardAffinizationCharts

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original chart affinizations form a natural transformation to the actual spectra. -/
def affinization : sourceDiagram f ⟶ PushforwardAffineDiagram.spectra f where
  app U := (f ⁻¹ᵁ U.1).toSpecΓ
  naturality {U V} i :=
    (Scheme.Opens.toSpecΓ_SpecMap_map (f ⁻¹ᵁ U.1) (f ⁻¹ᵁ V.1)
      (preimageLE f i)).symm

/-- Each chart map lands in the spectrum of the original inverse-image section ring. -/
@[simp] theorem affinization_app (U : Y.AffineZariskiSite) :
    (affinization f).app U = (f ⁻¹ᵁ U.1).toSpecΓ := rfl

end KltDP.Geometry.PushforwardAffinizationCharts
