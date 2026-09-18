import KltDP.Geometry.AffineCanonicalDifferenceFromSquare

/-!
# Affine positivity from a derived target identification

The target isomorphism stays a variable throughout the original native and
Cartier calculation. The supplied existential contains the actual original
square; no coefficient, order, or compatibility conclusion is assumed.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineCanonicalDifferenceFromSquare

open CartierRationalCoordinate OpenImmersionRational
open AffineDifferentialExteriorStalkEvaluation (originalStalkRing stalkGroundAlgebra)

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

local instance witnessOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- Genuine native parameter data and the original differential-coordinate
square force positivity of the original signed Cartier difference. -/
theorem order_difference_pos_of_target_identification
    (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B]
    (sA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k))
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) [GenericPointPreserving q]
    (hqbase : q ≫ sA = sB)
    (hA : sA = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hB : sB = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (p : PrimeSpectrum B)
    [IsDiscreteValuationRing ((Spec (CommRingCat.of B)).presheaf.stalk p)]
    (bA : Basis (Fin 2) A (KaehlerDifferential k A))
    (bB : Basis (Fin 2) B (KaehlerDifferential k B))
    (DA : CartierDivisor (Spec (CommRingCat.of A)))
    (DB : CartierDivisor (Spec (CommRingCat.of B)))
    (eB : cartierDivisorModule (Spec (CommRingCat.of B)) DB ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2)
    (hwitness : ∃ eA : cartierDivisorModule (Spec (CommRingCat.of A)) DA ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2,
      ∃ (Z : (Spec (CommRingCat.of B)).Opens) (hne : Nonempty Z.toScheme),
      letI : Nonempty Z.toScheme := hne
      letI : IsIntegral Z.toScheme := isIntegral_of_isOpenImmersion Z.ι
      ∃ ht : IsOpenImmersion (Z.ι ≫ q),
        letI : IsOpenImmersion (Z.ι ≫ q) := ht
        (schemeModulePullback Z.ι).map
            (SchemeKaehlerExteriorPullbackTransport.map sA q sB hqbase 2 ≫
              coordinate (Spec (CommRingCat.of B)) DB
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2) eB) ≫
            (rationalModulePullbackIso Z.ι).hom =
          (schemeModulePullbackCompIso Z.ι q).hom.app
              (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) ≫
            (schemeModulePullback (Z.ι ≫ q)).map
              (coordinate (Spec (CommRingCat.of A)) DA
                (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA) ≫
              (rationalModulePullbackIso (Z.ι ≫ q)).hom)
    (cT : CartierEquationChart (Spec (CommRingCat.of A)) DA)
    (cS : CartierEquationChart (Spec (CommRingCat.of B)) DB)
    (hST : cS.openSet ≤ q ⁻¹ᵁ cT.openSet) (hpS : p ∈ cS.openSet)
    (vA : Fin 2 → A)
    (hvA : ∀ t, StructureSheaf.toStalk A (q.base p) (vA t) ∈
      IsLocalRing.maximalIdeal (originalStalkRing A (q.base p))) :
    letI := stalkGroundAlgebra (k := k) (A := A) (p := q.base p)
    ∀ bₚ : Basis (Fin 2) (originalStalkRing A (q.base p))
        (KaehlerDifferential k (originalStalkRing A (q.base p))),
      (∀ t, bₚ t = KaehlerDifferential.D k (originalStalkRing A (q.base p))
        (StructureSheaf.toStalk A (q.base p) (vA t))) →
      0 < cartierOrderAt (Spec (CommRingCat.of B)) DB p -
        cartierOrderAt (Spec (CommRingCat.of B))
          (DominantCartierPullback.pullbackHom q DA) p := by
  obtain ⟨eA, hsquare⟩ := hwitness
  exact order_difference_pos k A B sA sB q hqbase hA hB p bA bB DA DB eA eB
    hsquare cT cS hST hpS vA hvA

end KltDP.Geometry.AffineCanonicalDifferenceFromSquare

#check @KltDP.Geometry.AffineCanonicalDifferenceFromSquare.order_difference_pos_of_target_identification
#print axioms KltDP.Geometry.AffineCanonicalDifferenceFromSquare.order_difference_pos_of_target_identification
