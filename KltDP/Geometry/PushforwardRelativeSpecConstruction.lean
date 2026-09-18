import KltDP.Geometry.PushforwardRelativeGluingData
import KltDP.Geometry.PushforwardAffinizationTriangle
import KltDP.Compatibility.RelativeGluingColimit

/-!
# The actual relative spectrum of the original pushforward algebra

The target is the constructed gluing of the original affine section-ring
spectra. Its canonical map from the original source is obtained by gluing
the original open affinizations. Their already-proved chart triangles
give the original global factorization, and every target chart square
is cartesian. No factorization or colimit is supplied as an assumption.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Limits
universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

open Scheme.AffineZariskiSite PushforwardAffinizationCharts
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The scheme glued from the original pushforward section-ring spectra. -/
def relativeSpec : Scheme.{u} := (datum f).glued

/-- Its original canonical map to the original base scheme. -/
def toBase : relativeSpec f ⟶ Y := (datum f).toBase

/-- The actual inclusion of an original affine section-ring spectrum. -/
def chart (U : Y.AffineZariskiSite) : Spec Γ(X, f ⁻¹ᵁ U.1) ⟶ relativeSpec f :=
  colimit.ι (datum f).functor U

instance chart_isOpenImmersion (U : Y.AffineZariskiSite) :
    IsOpenImmersion (chart f U) := by
  dsimp [chart]
  infer_instance

/-- The original source-chart affinizations, followed by the constructed chart inclusions. -/
def sourceToRelativeSpecCocone : Cocone (sourceDiagram f) where
  pt := relativeSpec f
  ι := affinization f ≫ (colimit.cocone (datum f).functor).ι

/-- The canonical map from the original source, obtained by the proved source-cover colimit. -/
def fromSource : X ⟶ relativeSpec f :=
  (sourceIsColimit f).desc (sourceToRelativeSpecCocone f)

/-- On every actual source chart this is precisely the original affinization map. -/
@[reassoc] theorem source_ι_fromSource (U : Y.AffineZariskiSite) :
    (f ⁻¹ᵁ U.1).ι ≫ fromSource f = (f ⁻¹ᵁ U.1).toSpecΓ ≫ chart f U :=
  (sourceIsColimit f).fac (sourceToRelativeSpecCocone f) U

/-- The constructed factorization recovers the exact original morphism. -/
@[reassoc] theorem fromSource_toBase : fromSource f ≫ toBase f = f := by
  apply (sourceCover f).hom_ext
  intro U
  change (f ⁻¹ᵁ U.1).ι ≫ fromSource f ≫ toBase f = (f ⁻¹ᵁ U.1).ι ≫ f
  rw [source_ι_fromSource_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ colimit.ι (datum f).functor U ≫
    (datum f).toBase = (f ⁻¹ᵁ U.1).ι ≫ f
  rw [Scheme.Cover.RelativeGluingData.ι_toBase]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app U.1) ≫ U.2.fromSpec =
    (f ⁻¹ᵁ U.1).ι ≫ f
  exact affinization_toBase_fromSpec f U

/-- The original affine-ring chart is the actual inverse-image chart over the base. -/
theorem chart_isPullback (U : Y.AffineZariskiSite) :
    IsPullback (Spec.map (f.app U.1) ≫ U.2.isoSpec.inv)
      (chart f U) U.1.ι (toBase f) :=
  (datum f).isPullback_natTrans_ι_toBase U

end KltDP.Geometry.PushforwardRelativeSpec
