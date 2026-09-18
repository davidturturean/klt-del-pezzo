import KltDP.Geometry.PushforwardRelativeSpecSourceCharts
import KltDP.Geometry.StructureSheafIsoPullbackTransport
import KltDP.Geometry.StructureSheafIsoLocal

/-!
# The original relative-spectrum map has the canonical pushforward-O isomorphism

The original source-chart square is cartesian, so the already-proved
open-affinization structure-sheaf isomorphism applies on each constructed
target chart. Target locality gives the original global canonical map.
Only qcqs is needed; no properness, normality or connected-fibre premise
is used to prove this clause.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The actual source map induces an isomorphism of the original structure sheaf
with its original pushforward. -/
theorem fromSource_c_isIso : IsIso (fromSource f).c := by
  apply StructureSheafIsoLocal.c_isIso_of_restrict_cover (fromSource f)
    (fun U : Y.AffineZariskiSite => (chart f U).opensRange)
  · exact (datum f).cover.iSup_opensRange
  · intro U
    letI : IsIso (f ⁻¹ᵁ U.1).toSpecΓ.c :=
      OpenAffinizationStructureSheaf.preimage_toSpecΓ_c_isIso f U
    exact StructureSheafIsoPullbackTransport.restrict_c_isIso_of_isPullback
      (f ⁻¹ᵁ U.1).toSpecΓ (f ⁻¹ᵁ U.1).ι (chart f U) (fromSource f)
      (fromSource_chart_isPullback f U)

end KltDP.Geometry.PushforwardRelativeSpec
