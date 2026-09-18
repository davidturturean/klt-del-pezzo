import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback

/-!
# Congruence for the original normalized open canonical coordinate

Only the supplied coordinate equality is transported. The
actual exterior differential and rational pullback comparison remain the
ones already proved for that same map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (σX : X ⟶ Spec (CommRingCat.of k)) (σY : Y ⟶ Spec (CommRingCat.of k))

local instance openGeneric (f : Y ⟶ X) [IsOpenImmersion f] : GenericPointPreserving f :=
  ⟨genericPoint_eq_of_isOpenImmersion f⟩

/-- Equality of the actual coordinates is preserved by normalized pullback
through the original exterior differential of an open immersion. -/
theorem canonicalOpenPullback_coordinate_congr
    (f : Y ⟶ X) [IsOpenImmersion f] (hf : f ≫ σX = σY)
    (D E : CartierDivisor X)
    (eD : cartierDivisorModule X D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior σX 2)
    (eE : cartierDivisorModule X E ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior σX 2)
    (h : coordinate X D _ eD = coordinate X E _ eE) :
    coordinate Y (DominantCartierPullback.pullbackHom f D) _
        (canonicalOpenPullbackIso f σX σY hf D eD) =
      coordinate Y (DominantCartierPullback.pullbackHom f E) _
        (canonicalOpenPullbackIso f σX σY hf E eE) := by
  letI := SchemeKaehlerExteriorPullbackTransport.map_isIso σX f σY hf 2
  apply (cancel_epi (SchemeKaehlerExteriorPullbackTransport.map σX f σY hf 2)).mp
  rw [map_comp_coordinate_canonicalOpenPullbackIso,
    map_comp_coordinate_canonicalOpenPullbackIso, h]

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.canonicalOpenPullback_coordinate_congr
