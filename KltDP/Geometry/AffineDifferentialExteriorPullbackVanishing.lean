import KltDP.Geometry.AffineDifferentialExteriorPullbackStalk
import KltDP.RingTheory.DerivationCommonFactorWedge

/-!
# Vanishing of the actual affine exterior pullback coordinate

The original intrinsic pullback, applied to its original adjunction-unit
wedge and evaluated at the original source stalk, has nonunit scalar
coordinates when both target germs vanish and the source stalk is a DVR.
The native comparison and the original scheme stalk map are retained.
This does not yet identify a Cartier discrepancy coefficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorPullbackVanishing

open AffineDifferentialExteriorPullbackStalk
open AffineDifferentialExteriorStalkEvaluation (originalStalkRing stalkGroundAlgebra)
open KltDP.Examples.FrobeniusBlowupDifferential

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (p : PrimeSpectrum B)

local notation "Bₚ" => originalStalkRing B p

/-- Every scalar evaluation of this original pulled wedge belongs to the
actual source maximal ideal. The vanishing assumptions concern the original
target functions, not a chosen value for their pullback coordinate. -/
theorem coefficient_mem_maximalIdeal [IsDomain Bₚ] [IsDiscreteValuationRing Bₚ]
    (b : Basis (Fin 2) B (KaehlerDifferential k B)) (v : Fin 2 → A)
    (hv : ∀ i, StructureSheaf.toStalk A ((Spec.map (CommRingCat.ofHom (algebraMap A B))).base p) (v i) ∈
      IsLocalRing.maximalIdeal (originalStalkRing A ((Spec.map (CommRingCat.ofHom (algebraMap A B))).base p))) :
    letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
    ∀ ell : (⋀[Bₚ]^2 (KaehlerDifferential k Bₚ)) →ₗ[Bₚ] Bₚ,
      ell (pullbackStalkMap k A B p b
        ((pullbackPresheaf k A B 2).germ ⊤ p trivial
          (originalUnitWedge k A B 2 v))) ∈ IsLocalRing.maximalIdeal Bₚ := by
  letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
  intro ell
  rw [pullbackStalkMap_germ_unit_stalkMap]
  let w : Fin 2 → Bₚ := fun i =>
    ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap p).hom (StructureSheaf.toStalk A ((Spec.map (CommRingCat.ofHom (algebraMap A B))).base p) (v i))
  have hw : ∀ i, w i ∈ IsLocalRing.maximalIdeal Bₚ := fun i =>
    map_nonunit ((Spec.map (CommRingCat.ofHom (algebraMap A B))).stalkMap p).hom _ (hv i)
  have heta : (fun i => KaehlerDifferential.D k Bₚ (w i)) =
      ![KaehlerDifferential.D k Bₚ (w 0), KaehlerDifferential.D k Bₚ (w 1)] := by
    funext i
    fin_cases i <;> rfl
  change ell (exteriorPower.ιMulti Bₚ 2
    (fun i => KaehlerDifferential.D k Bₚ (w i))) ∈ _
  rw [heta]
  exact KltDP.RingTheory.DerivationCommonFactorWedge.coefficient_mem_maximalIdeal
    (KaehlerDifferential.D k Bₚ) ell (w 0) (w 1) (hw 0) (hw 1)

end KltDP.Geometry.AffineDifferentialExteriorPullbackVanishing

#check @KltDP.Geometry.AffineDifferentialExteriorPullbackVanishing.coefficient_mem_maximalIdeal
#print axioms KltDP.Geometry.AffineDifferentialExteriorPullbackVanishing.coefficient_mem_maximalIdeal
