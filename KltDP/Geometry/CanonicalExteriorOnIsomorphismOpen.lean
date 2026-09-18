import KltDP.Geometry.SchemeKaehlerExteriorOpenRestriction
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso
import KltDP.Geometry.CanonicalExteriorIsoCancellation

/-!
# Original differential exteriors on an isomorphism open

Compare the actual exterior differential sheaf on the target open with the
original source exterior, restricted to its preimage. All transports use the
original structure triangle and the actual scheme restriction square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalExteriorOnIsomorphismOpen

open SchemeKaehlerSheaf

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (σ : Y ⟶ Spec (CommRingCat.of k))
    (π : X ⟶ Y) (hπ : π ≫ σ = f) (U : Y.Opens)

include hπ in
/-- The structure equality is derived from the actual restriction square. -/
theorem restriction_structure :
    (π ∣_ U) ≫ (U.ι ≫ σ) = (π ⁻¹ᵁ U).ι ≫ f := by
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hπ]

variable [IsIso (π ∣_ U)] (n : ℕ)

/-- Pull back the target-open exterior to the intrinsic exterior on the source open. -/
def intrinsicIso :
    (schemeModulePullback (π ∣_ U)).obj
        (SchemeExteriorPower.sheaf (baseRingSheaf (U.ι ≫ σ)) n) ≅
      SchemeExteriorPower.sheaf (baseRingSheaf ((π ⁻¹ᵁ U).ι ≫ f)) n :=
  letI := SchemeKaehlerExteriorPullbackTransport.map_isIso (U.ι ≫ σ) (π ∣_ U)
    ((π ⁻¹ᵁ U).ι ≫ f) (restriction_structure f σ π hπ U) n
  asIso (SchemeKaehlerExteriorPullbackTransport.map (U.ι ≫ σ) (π ∣_ U)
    ((π ⁻¹ᵁ U).ι ≫ f) (restriction_structure f σ π hπ U) n)

/-- The target-open exterior pulls back to the original source exterior pullback. -/
def pullbackIso :
    (schemeModulePullback (π ∣_ U)).obj
        (SchemeExteriorPower.sheaf (baseRingSheaf (U.ι ≫ σ)) n) ≅
      (schemeModulePullback (π ⁻¹ᵁ U).ι).obj
        (SchemeExteriorPower.sheaf (baseRingSheaf f) n) :=
  CanonicalExteriorIsoCancellation.comparison (intrinsicIso f σ π hπ U n)
    (SchemeKaehlerExteriorOpenRestriction.pullbackIso f (π ⁻¹ᵁ U).ι n)

/-- The same comparison with the literal original source restriction as target. -/
def restrictionIso :
    (schemeModulePullback (π ∣_ U)).obj
        (SchemeExteriorPower.sheaf (baseRingSheaf (U.ι ≫ σ)) n) ≅
      (SchemeModuleRestriction.restriction (π ⁻¹ᵁ U).ι).obj
        (SchemeExteriorPower.sheaf (baseRingSheaf f) n) :=
  CanonicalExteriorIsoCancellation.comparison (intrinsicIso f σ π hπ U n)
    (SchemeKaehlerExteriorOpenRestriction.restrictionIso f (π ⁻¹ᵁ U).ι n)

/-- The forward intrinsic comparison is the original transported exterior differential. -/
theorem intrinsicIso_hom :
    (intrinsicIso f σ π hπ U n).hom =
      SchemeKaehlerExteriorPullbackTransport.map (U.ι ≫ σ) (π ∣_ U)
        ((π ⁻¹ᵁ U).ι ≫ f) (restriction_structure f σ π hπ U) n := by
  rfl

/-- The original source-open differential recovers that same intrinsic map. -/
theorem pullbackIso_hom_comp :
    (pullbackIso f σ π hπ U n).hom ≫
        (SchemeKaehlerExteriorOpenRestriction.pullbackIso f (π ⁻¹ᵁ U).ι n).hom =
      SchemeKaehlerExteriorPullbackTransport.map (U.ι ≫ σ) (π ∣_ U)
        ((π ⁻¹ᵁ U).ι ≫ f) (restriction_structure f σ π hπ U) n := by
  exact (CanonicalExteriorIsoCancellation.comparison_hom_comp
    (intrinsicIso f σ π hπ U n)
    (SchemeKaehlerExteriorOpenRestriction.pullbackIso f (π ⁻¹ᵁ U).ι n)).trans
      (intrinsicIso_hom f σ π hπ U n)

end KltDP.Geometry.CanonicalExteriorOnIsomorphismOpen
