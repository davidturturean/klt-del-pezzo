import KltDP.Geometry.OriginalDifferentialCoefficientOrderSquare
import KltDP.Geometry.AffineDifferentialCartierCoefficientNormalization
import KltDP.Geometry.OriginalSectionGermOrder

/-!
# Positive Cartier difference from the original affine square

The native maximal-ideal calculation and the original square-to-order
calculation are joined while both Cartier isomorphisms remain abstract.
Only the integer Cartier difference survives in the conclusion; no
concrete canonical frame occurs in that result type.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineCanonicalDifferenceFromSquare

open CartierRationalCoordinate NormalizedDifferentialCoefficientOrder OpenImmersionRational
open AffineDifferentialExteriorStalkEvaluation (originalStalkRing stalkGroundAlgebra)

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

local instance squareOpenGeneric {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    (i : A ⟶ B) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

/-- Genuine native parameter data and the original differential-coordinate
square force positivity of the original signed Cartier difference. -/
theorem order_difference_pos
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
    (eA : cartierDivisorModule (Spec (CommRingCat.of A)) DA ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2)
    (eB : cartierDivisorModule (Spec (CommRingCat.of B)) DB ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2)
    (hsquare : ∃ (Z : (Spec (CommRingCat.of B)).Opens) (hne : Nonempty Z.toScheme),
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
  letI := stalkGroundAlgebra (k := k) (A := A) (p := q.base p)
  intro bₚ hbₚ
  let M := SmoothCanonicalExteriorComparison.relativeDifferentialExterior sB 2
  let t := imageSection sA sB q hqbase cT.openSet
    (frame (Spec (CommRingCat.of A)) DA
      (SmoothCanonicalExteriorComparison.relativeDifferentialExterior sA 2) eA cT)
  let s := M.val.map (homOfLE hST).op t
  let a := sectionCoefficient (Spec (CommRingCat.of B)) DB M eB cS s
  let r := Units.map (functionFieldMap q).hom.toMonoidHom cT.equation⁻¹ * cS.equation
  have horder := OriginalDifferentialCoefficientOrder.coefficient_order_of_exists_open_square
    sA sB q hqbase DA DB eA eB hsquare cS cT hST p hpS
  have hm := AffineDifferentialCartierCoefficientNormalization.sectionCoefficient_image_frame_mem_maximalIdeal
    k A B sA sB q hqbase hA hB p bA bB DA DB eA eB cT cS hST hpS vA hvA bₚ hbₚ
  have hpos : 0 < stalkDivisorOrder (Spec (CommRingCat.of B)) p r :=
    OriginalSectionGermOrder.order_pos_of_germ_mem_maximalIdeal
      (Spec (CommRingCat.of B)) cS.openSet p hpS a r horder.1 hm
  exact horder.2 ▸ hpos

end KltDP.Geometry.AffineCanonicalDifferenceFromSquare

#check @KltDP.Geometry.AffineCanonicalDifferenceFromSquare.order_difference_pos
#print axioms KltDP.Geometry.AffineCanonicalDifferenceFromSquare.order_difference_pos
