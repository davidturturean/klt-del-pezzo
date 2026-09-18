import KltDP.Geometry.CartierRationalCoordinateOpenPullback
import KltDP.Geometry.DominantCartierPullbackOpenRestriction
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso
import KltDP.Geometry.SmoothCanonicalExteriorComparison

/-!
# The same rational form under the original open differential

The divisor is the existing signed Cartier pullback. Its module identification
is constructed from the normalized original open Cartier pullback and the
actual second exterior differential. The resulting rational-coordinate square
has no scalar or independent canonical-choice compatibility premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

open OpenImmersionRational

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f]

local instance : GenericPointPreserving f := ⟨genericPoint_eq_of_isOpenImmersion f⟩

/-- The same normalized module identification with the existing signed
Cartier pullback as its literal divisor argument. -/
def signedOpenPullbackIso (D : CartierDivisor X) (M : X.Modules)
    (e : cartierDivisorModule X D ≅ M) :
    cartierDivisorModule Y (DominantCartierPullback.pullbackHom f D) ≅
      (schemeModulePullback f).obj M :=
  eqToIso (congrArg (cartierDivisorModule Y)
    (congrArg (fun a : CartierDivisor X →+ CartierDivisor Y => a D)
      (DominantCartierPullback.pullbackHom_eq_cartierRestrictionHom f))) ≪≫
    openPullbackIso f D M e

/-- The original signed Cartier pullback retains the same rational coordinate. -/
theorem coordinate_signedOpenPullbackIso (D : CartierDivisor X) (M : X.Modules)
    (e : cartierDivisorModule X D ≅ M) :
    coordinate Y (DominantCartierPullback.pullbackHom f D)
        ((schemeModulePullback f).obj M) (signedOpenPullbackIso f D M e) =
      (schemeModulePullback f).map (coordinate X D M e) ≫
        (rationalModulePullbackIso f).hom := by
  have hD : DominantCartierPullback.pullbackHom f D = cartierRestrictionHom f D :=
    congrArg (fun a : CartierDivisor X →+ CartierDivisor Y => a D)
      (DominantCartierPullback.pullbackHom_eq_cartierRestrictionHom f)
  exact (coordinate_eqToIso_left Y (DominantCartierPullback.pullbackHom f D)
    (cartierRestrictionHom f D) hD ((schemeModulePullback f).obj M)
      (openPullbackIso f D M e)).trans (coordinate_openPullbackIso f D M e)

/-- The canonical identification constructed through the actual original
exterior differential and normalized signed Cartier pullback. -/
def canonicalOpenPullbackIso
    {k : Type u} [CommRing k]
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ fX = fY) (D : CartierDivisor X)
    (e : cartierDivisorModule X D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior fX 2) :
    cartierDivisorModule Y (DominantCartierPullback.pullbackHom f D) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior fY 2 := by
  letI := SchemeKaehlerExteriorPullbackTransport.map_isIso fX f fY hf 2
  exact signedOpenPullbackIso f D _ e ≪≫
    asIso (SchemeKaehlerExteriorPullbackTransport.map fX f fY hf 2)

/-- The original exterior differential preserves the rational coordinate
of the constructed canonical representative through the original field map. -/
theorem map_comp_coordinate_canonicalOpenPullbackIso
    {k : Type u} [CommRing k]
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ fX = fY) (D : CartierDivisor X)
    (e : cartierDivisorModule X D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior fX 2) :
    SchemeKaehlerExteriorPullbackTransport.map fX f fY hf 2 ≫
        coordinate Y (DominantCartierPullback.pullbackHom f D)
          (SmoothCanonicalExteriorComparison.relativeDifferentialExterior fY 2)
          (canonicalOpenPullbackIso f fX fY hf D e) =
      (schemeModulePullback f).map (coordinate X D
          (SmoothCanonicalExteriorComparison.relativeDifferentialExterior fX 2) e) ≫
        (rationalModulePullbackIso f).hom := by
  letI := SchemeKaehlerExteriorPullbackTransport.map_isIso fX f fY hf 2
  change (asIso (SchemeKaehlerExteriorPullbackTransport.map fX f fY hf 2)).hom ≫
      coordinate Y (DominantCartierPullback.pullbackHom f D) _
        (signedOpenPullbackIso f D _ e ≪≫
          asIso (SchemeKaehlerExteriorPullbackTransport.map fX f fY hf 2)) = _
  rw [hom_comp_coordinate_trans]
  exact coordinate_signedOpenPullbackIso f D _ e

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.map_comp_coordinate_canonicalOpenPullbackIso
#print axioms KltDP.Geometry.CartierRationalCoordinate.coordinate_signedOpenPullbackIso
#print axioms KltDP.Geometry.CartierRationalCoordinate.map_comp_coordinate_canonicalOpenPullbackIso
