import KltDP.Geometry.CanonicalPrincipalShiftCoordinate
import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback
import KltDP.Geometry.RationalOpenPullbackMultiplication

/-!
# The original corrected canonical coordinate on a smaller open

The actual principal correction commutes with normalized open pullback
at the level of rational coordinates. Its scalar is transported by the
original open-immersion function-field map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

open OpenImmersionRational DominantCartierPullback

attribute [local irreducible] canonicalOpenPullbackIso

local instance shiftOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (f : A ⟶ B) [IsOpenImmersion f] : GenericPointPreserving f :=
  ⟨genericPoint_eq_of_isOpenImmersion f⟩

/-- The actual principal-shift coordinate restricts by the original scalar map. -/
theorem coordinate_rescaleIso_openPullback
    {k : Type u} [CommRing k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f]
    (sX : X ⟶ Spec (CommRingCat.of k)) (sY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ sX = sY) (D : CartierDivisor X)
    (e : cartierDivisorModule X D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sX 2)
    (q : X.functionFieldˣ) :
    coordinate Y (pullbackHom f (rescaleDivisor X D q))
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sY 2)
        (canonicalOpenPullbackIso f sX sY hf (rescaleDivisor X D q)
          (rescaleIso X D
            (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sX 2) e q)) =
      coordinate Y (pullbackHom f D)
          (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sY 2)
          (canonicalOpenPullbackIso f sX sY hf D e) ≫
        (rationalFunctionMulIso Y
          (Units.map (functionFieldIso f).hom.hom.toMonoidHom q)).hom := by
  let M := SmoothCanonicalExteriorComparison.relativeDifferentialExterior sX 2
  let N := SmoothCanonicalExteriorComparison.relativeDifferentialExterior sY 2
  let d := SchemeKaehlerExteriorPullbackTransport.map sX f sY hf 2
  let c := coordinate Y (pullbackHom f D) N (canonicalOpenPullbackIso f sX sY hf D e)
  letI : IsIso d := SchemeKaehlerExteriorPullbackTransport.map_isIso sX f sY hf 2
  apply (cancel_epi d).mp
  calc
    _ = (schemeModulePullback f).map
        (coordinate X (rescaleDivisor X D q) M (rescaleIso X D M e q)) ≫
        (rationalModulePullbackIso f).hom :=
      map_comp_coordinate_canonicalOpenPullbackIso f sX sY hf
        (rescaleDivisor X D q) (rescaleIso X D M e q)
    _ = (schemeModulePullback f).map
        (coordinate X D M e ≫ (rationalFunctionMulIso X q).hom) ≫
        (rationalModulePullbackIso f).hom := by rw [coordinate_rescaleIso]
    _ = (schemeModulePullback f).map (coordinate X D M e) ≫
        ((schemeModulePullback f).map (rationalFunctionMulIso X q).hom ≫
          (rationalModulePullbackIso f).hom) := by rw [Functor.map_comp, Category.assoc]
    _ = (schemeModulePullback f).map (coordinate X D M e) ≫
        ((rationalModulePullbackIso f).hom ≫ (rationalFunctionMulIso Y
          (Units.map (functionFieldIso f).hom.hom.toMonoidHom q)).hom) := by
      rw [rationalModulePullbackIso_mul f q]
    _ = d ≫ (c ≫ (rationalFunctionMulIso Y
        (Units.map (functionFieldIso f).hom.hom.toMonoidHom q)).hom) := by
      rw [← Category.assoc, ← map_comp_coordinate_canonicalOpenPullbackIso
        f sX sY hf D e, Category.assoc]

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.coordinate_rescaleIso_openPullback
#print axioms KltDP.Geometry.CartierRationalCoordinate.coordinate_rescaleIso_openPullback
