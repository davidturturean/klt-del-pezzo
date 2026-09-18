import KltDP.Geometry.IntegralClosureSpectrumDiagram
import KltDP.Compatibility.RelativeGluingData
import KltDP.Compatibility.AffineZariskiDirectedCover

/-!
# Actual relative gluing data for the original pushforward algebra

Every object, transition and base map comes from the original rings of
sections. The cartesian-square property is proved from localization.
The integral-closure counterpart uses the actual integral-element
subalgebras, with its own proved canonical comparison.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PushforwardRelativeSpec

open Scheme.AffineZariskiSite
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- Original pushforward-section spectra over the original affine base cover. -/
def datum : Scheme.Cover.RelativeGluingData (directedCover Y) where
  functor := PushforwardAffineDiagram.spectra f
  natTrans := PushforwardAffineDiagram.toBaseSpectra f ≫ (restrictIsoSpec Y).inv
  equifibered := (PushforwardAffineDiagram.toBaseSpectra_equifibered f).comp
    (NatTrans.equifibered_of_isIso (restrictIsoSpec Y).inv)

/-- The actual integral-closure spectra satisfy the same relative gluing condition. -/
def normalizationDatum [UniversallyClosed f] :
    Scheme.Cover.RelativeGluingData (directedCover Y) where
  functor := IntegralClosureSpectrumDiagram.spectra f
  natTrans := IntegralClosureSpectrumDiagram.toBaseSpectra f ≫ (restrictIsoSpec Y).inv
  equifibered := (IntegralClosureSpectrumDiagram.toBaseSpectra_equifibered f).comp
    (NatTrans.equifibered_of_isIso (restrictIsoSpec Y).inv)

end KltDP.Geometry.PushforwardRelativeSpec
