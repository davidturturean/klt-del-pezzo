import KltDP.Geometry.AffineDifferentialCartierCoefficientMaximalIdeal
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Retaining the actual affine structure maps in the coefficient theorem

The structure equations are original chart equations. The pinned Spec/Γ
adjunction derives the affine ring map of the actual morphism. Dependent
substitution transports the same Cartier module identifications, the same
chart restrictions and the same differential image section.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineDifferentialCartierCoefficientNormalization

open SmoothCanonicalExteriorComparison CartierRationalCoordinate
open NormalizedDifferentialCoefficientOrder
open AffineDifferentialExteriorStalkEvaluation (originalStalkRing stalkGroundAlgebra)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B]
    (sA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (sB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k))
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (hqbase : q ≫ sA = sB)
    (hA : sA = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hB : sB = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (p : PrimeSpectrum B)
    [hDomain : IsDomain (originalStalkRing B p)]
    [hDVR : IsDiscreteValuationRing (originalStalkRing B p)]
    (bA : Basis (Fin 2) A (KaehlerDifferential k A))
    (bB : Basis (Fin 2) B (KaehlerDifferential k B))
    (DT : CartierDivisor (Spec (CommRingCat.of A)))
    (DS : CartierDivisor (Spec (CommRingCat.of B)))
    (eT : cartierDivisorModule (Spec (CommRingCat.of A)) DT ≅
      relativeDifferentialExterior sA 2)
    (eS : cartierDivisorModule (Spec (CommRingCat.of B)) DS ≅
      relativeDifferentialExterior sB 2)
    (cT : CartierEquationChart (Spec (CommRingCat.of A)) DT)
    (cS : CartierEquationChart (Spec (CommRingCat.of B)) DS)
    (hST : cS.openSet ≤ q ⁻¹ᵁ cT.openSet) (hpS : p ∈ cS.openSet)
    (v : Fin 2 → A)
    (hv : ∀ i, StructureSheaf.toStalk A (q.base p) (v i) ∈
      IsLocalRing.maximalIdeal (originalStalkRing A (q.base p)))

include hA hB bA bB hv hDomain hDVR in
/-- The coefficient belongs to the maximal ideal with the actual original
structure maps and Cartier identifications still present in the conclusion. -/
theorem sectionCoefficient_image_frame_mem_maximalIdeal :
    letI := stalkGroundAlgebra (k := k) (A := A) (p := q.base p)
    ∀ bₚ : Basis (Fin 2) (originalStalkRing A (q.base p))
        (KaehlerDifferential k (originalStalkRing A (q.base p))),
      (∀ i, bₚ i = KaehlerDifferential.D k (originalStalkRing A (q.base p))
        (StructureSheaf.toStalk A (q.base p) (v i))) →
      (Spec (CommRingCat.of B)).presheaf.germ cS.openSet p hpS
        (sectionCoefficient (Spec (CommRingCat.of B)) DS _ eS cS
          ((relativeDifferentialExterior sB 2).val.map (homOfLE hST).op
            (imageSection sA sB q hqbase cT.openSet
              (frame (Spec (CommRingCat.of A)) DT _ eT cT)))) ∈
        IsLocalRing.maximalIdeal (originalStalkRing B p) := by
  obtain ⟨φ, hq⟩ : ∃ φ : A →+* B, q = Spec.map (CommRingCat.ofHom φ) :=
    ⟨(Spec.preimage q).hom, (Spec.map_preimage q).symm⟩
  subst sA
  subst sB
  subst q
  exact AffineDifferentialCartierCoefficientMaximalIdeal.sectionCoefficient_image_frame_mem_maximalIdeal
    k A B φ hqbase p bA bB DT DS eT eS cT cS hST hpS v hv

end KltDP.Geometry.AffineDifferentialCartierCoefficientNormalization

#check @KltDP.Geometry.AffineDifferentialCartierCoefficientNormalization.sectionCoefficient_image_frame_mem_maximalIdeal
#print axioms KltDP.Geometry.AffineDifferentialCartierCoefficientNormalization.sectionCoefficient_image_frame_mem_maximalIdeal
