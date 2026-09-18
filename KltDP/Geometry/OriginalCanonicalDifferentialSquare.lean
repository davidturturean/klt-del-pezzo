import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback

/-!
# The original canonical differential square as a named proposition

This internal proof package retains the actual schemes, structure maps,
Cartier divisors and source identification. Its sole field is the original
nonempty-open differential-coordinate square, including its target witness.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

open CartierRationalCoordinate OpenImmersionRational

local instance namedSquareOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- An actual original differential square with a target Cartier identification.
This is a proof package; the later geometric producer proves its only field. -/
structure OriginalCanonicalDifferentialSquare
    {k : Type u} [CommRing k] {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (sA : A ⟶ Spec (CommRingCat.of k)) (sB : B ⟶ Spec (CommRingCat.of k))
    (q : B ⟶ A) (hqbase : q ≫ sA = sB)
    (DA : CartierDivisor A) (DB : CartierDivisor B)
    (eB : cartierDivisorModule B DB ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2) : Prop where
  witness : ∃ eA : cartierDivisorModule A DA ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2,
      ∃ (Z : B.Opens) (hne : Nonempty Z.toScheme),
      letI : Nonempty Z.toScheme := hne
      letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
      ∃ ht : IsOpenImmersion (Z.ι ≫ q),
        letI : IsOpenImmersion (Z.ι ≫ q) := ht
        (schemeModulePullback Z.ι).map
            (SchemeKaehlerExteriorPullbackTransport.map sA q sB hqbase 2 ≫
              coordinate B DB
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2) eB) ≫
            (rationalModulePullbackIso Z.ι).hom =
          (schemeModulePullbackCompIso Z.ι q).hom.app
              (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) ≫
            (schemeModulePullback (Z.ι ≫ q)).map
              (coordinate A DA
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA) ≫
              (rationalModulePullbackIso (Z.ι ≫ q)).hom

end KltDP.Geometry

#check @KltDP.Geometry.OriginalCanonicalDifferentialSquare
#check @KltDP.Geometry.OriginalCanonicalDifferentialSquare.witness
