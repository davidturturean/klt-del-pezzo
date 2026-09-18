import KltDP.Geometry.SmoothPointBlowupRefinedFactors
import KltDP.Geometry.AffineBlowupPrincipalRefinementCover
import KltDP.Geometry.SchemeModuleMonicFactorOnCharts
import KltDP.Geometry.AffinePlaneEtaleBlowupSmooth

/-!
# The original extended center and its two original generators

This small leaf keeps the center and generator equations separate from the
native chart-factor specialization. All maps and definitions are unchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

open AffineBlowup AffineBlowupChartBaseChange AffineBlowupTopDifferential
open AffineNativeTopDifferential
open KltDP.Examples.FrobeniusBlowupContact KltDP.Examples.FrobeniusBlowupSmooth

local instance affineCenterModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)

abbrev extendedCenter : Ideal S := Ideal.map φ.toRingHom (centerIdeal (k := k))

def generator (i : Bool) : extendedCenter k φ :=
  mappedElement centerIdeal φ.toRingHom (centerGenerator i)

theorem span_generator :
    Ideal.span (Set.range (fun i => (generator k φ i : S))) = extendedCenter k φ := by
  change Ideal.span (Set.range (fun i => φ (centerGenerator (k := k) i : planeRing k))) = _
  rw [Set.range_comp', ← Ideal.map_span, span_centerGenerator]
  rfl

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
