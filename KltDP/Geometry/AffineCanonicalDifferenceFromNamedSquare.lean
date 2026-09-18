import KltDP.Geometry.OriginalCanonicalDifferentialSquare
import KltDP.Geometry.AffineCanonicalDifferenceFromWitness

/-! The named original square feeds the affine positivity theorem. -/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineCanonicalDifferenceFromSquare

open AffineDifferentialExteriorStalkEvaluation (originalStalkRing stalkGroundAlgebra)

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] integralSchemeStalk_isDomain

/-- Genuine native parameter data and the original differential-coordinate
square force positivity of the original signed Cartier difference. -/
theorem order_difference_pos_of_named_square
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
    (hsquare : OriginalCanonicalDifferentialSquare sA sB q hqbase DA DB eB)
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
  exact order_difference_pos_of_target_identification k A B sA sB q hqbase hA hB
    p bA bB DA DB eB hsquare.witness cT cS hST hpS vA hvA

end KltDP.Geometry.AffineCanonicalDifferenceFromSquare

#check @KltDP.Geometry.AffineCanonicalDifferenceFromSquare.order_difference_pos_of_named_square
#print axioms KltDP.Geometry.AffineCanonicalDifferenceFromSquare.order_difference_pos_of_named_square
