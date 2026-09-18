import KltDP.Geometry.AffineSpecDifferentialImageStalk
import KltDP.Geometry.AffineDifferentialParameterCoefficientUnit
import KltDP.Geometry.DifferentialImageCartierCoefficient
import KltDP.Geometry.KaehlerLocalizedFrame
import KltDP.RingTheory.DerivationCommonFactorWedge

/-!
# The actual Cartier coefficient of the original differential image vanishes

The actual target parameter germs vanish and their native derivatives form a
basis. The original section coefficient of their wedge is consequently a unit.
On the source DVR, the literal differential image has every native scalar
coordinate in the maximal ideal. The original source Cartier frame is itself
primitive. These two derived units transfer vanishing to the coefficient of
the image of the original target Cartier frame.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialCartierCoefficientMaximalIdeal

open SchemeKaehlerSheaf SmoothCanonicalExteriorComparison CartierRationalCoordinate
open NormalizedDifferentialCoefficientOrder AffineDifferentialExteriorOriginalStalk
open AffineDifferentialExteriorStalkEvaluation
  (originalStalkRing stalkAffineAlgebra stalkGroundAlgebra stalkScalarTower stalkExteriorModule)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem mem_of_mul_unit {R : Type u} [CommRing R] [IsLocalRing R]
    {a z : R} (hz : IsUnit z) (h : a * z ∈ IsLocalRing.maximalIdeal R) :
    a ∈ IsLocalRing.maximalIdeal R := by
  have hm : (IsLocalRing.maximalIdeal R).IsPrime := inferInstance
  exact (hm.mem_or_mem h).resolve_right (IsLocalRing.not_mem_maximalIdeal.mpr hz)

private theorem mem_of_unit_mul {R : Type u} [CommRing R] [IsLocalRing R]
    {a z : R} (hz : IsUnit z) (h : z * a ∈ IsLocalRing.maximalIdeal R) :
    a ∈ IsLocalRing.maximalIdeal R := by
  have hm : (IsLocalRing.maximalIdeal R).IsPrime := inferInstance
  exact (hm.mem_or_mem h).resolve_left (IsLocalRing.not_mem_maximalIdeal.mpr hz)

private theorem germ_appLE {X Y : Scheme.{u}} (π : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ π ⁻¹ᵁ U)
    (p : Y) (hp : p ∈ V) (a : Γ(X, U)) :
    π.stalkMap p (X.presheaf.germ U (π.base p) (hVU hp) a) =
      Y.presheaf.germ V p hp (π.appLE U V hVU a) := by
  calc
    _ = Y.presheaf.germ (π ⁻¹ᵁ U) p (hVU hp) (π.app U a) :=
      Scheme.stalkMap_germ_apply π U p (hVU hp) a
    _ = Y.presheaf.germ V p hp
        (Y.presheaf.map (homOfLE hVU).op (π.app U a)) :=
      (Y.presheaf.germ_res_apply (homOfLE hVU) p hp (π.app U a)).symm
    _ = _ := rfl

variable (k A B : Type u) [CommRing k] [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra k A] [Algebra k B]
    (φ : A →+* B)


variable (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k A)) =
        Spec.map (CommRingCat.ofHom (algebraMap k B))) (p : PrimeSpectrum B)
    [hDomain : IsDomain (originalStalkRing B p)]
    [hDVR : IsDiscreteValuationRing (originalStalkRing B p)]
    (bA : Basis (Fin 2) A (KaehlerDifferential k A))
    (bB : Basis (Fin 2) B (KaehlerDifferential k B))
    (DT : CartierDivisor (Spec (CommRingCat.of A)))
    (DS : CartierDivisor (Spec (CommRingCat.of B)))
    (eT : cartierDivisorModule (Spec (CommRingCat.of A)) DT ≅
      relativeDifferentialExterior (Spec.map (CommRingCat.ofHom (algebraMap k A))) 2)
    (eS : cartierDivisorModule (Spec (CommRingCat.of B)) DS ≅
      relativeDifferentialExterior (Spec.map (CommRingCat.ofHom (algebraMap k B))) 2)
    (cT : CartierEquationChart (Spec (CommRingCat.of A)) DT)
    (cS : CartierEquationChart (Spec (CommRingCat.of B)) DS)
    (hST : cS.openSet ≤ (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ cT.openSet) (hpS : p ∈ cS.openSet)
    (v : Fin 2 → A)
    (hv : ∀ i, StructureSheaf.toStalk A (((Spec.map (CommRingCat.ofHom φ))).base p) (v i) ∈
      IsLocalRing.maximalIdeal (originalStalkRing A (((Spec.map (CommRingCat.ofHom φ))).base p)))

include bA bB hv hDomain hDVR in
/-- No coefficient or unit equality is supplied: the conclusion concerns
the literal coefficient of the original target Cartier frame's image. -/
theorem sectionCoefficient_image_frame_mem_maximalIdeal :
    letI := stalkGroundAlgebra (k := k) (A := A) (p := ((Spec.map (CommRingCat.ofHom φ))).base p)
    ∀ bₚ : Basis (Fin 2) (originalStalkRing A (((Spec.map (CommRingCat.ofHom φ))).base p))
        (KaehlerDifferential k (originalStalkRing A (((Spec.map (CommRingCat.ofHom φ))).base p))),
      (∀ i, bₚ i = KaehlerDifferential.D k (originalStalkRing A (((Spec.map (CommRingCat.ofHom φ))).base p))
        (StructureSheaf.toStalk A (((Spec.map (CommRingCat.ofHom φ))).base p) (v i))) →
      (Spec (CommRingCat.of B)).presheaf.germ cS.openSet p hpS
        (sectionCoefficient (Spec (CommRingCat.of B)) DS _ eS cS
          ((relativeDifferentialExterior (Spec.map (CommRingCat.ofHom (algebraMap k B))) 2).val.map (homOfLE hST).op
            (imageSection (Spec.map (CommRingCat.ofHom (algebraMap k A))) (Spec.map (CommRingCat.ofHom (algebraMap k B))) (Spec.map (CommRingCat.ofHom φ)) hφ cT.openSet
              (frame (Spec (CommRingCat.of A)) DT _ eT cT)))) ∈
        IsLocalRing.maximalIdeal (originalStalkRing B p) := by
  dsimp only
  letI := stalkGroundAlgebra (k := k) (A := A) (p := ((Spec.map (CommRingCat.ofHom φ))).base p)
  intro bₚ hbₚ
  letI := stalkAffineAlgebra (A := B) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := B) (p := p)
  letI := stalkScalarTower (k := k) (A := B) (p := p)
  letI := stalkExteriorModule k B p 2
  letI : IsLocalization.AtPrime (originalStalkRing B p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B p
  letI sm := stalkModuleOfBasis k B p bB
  letI : SMul (originalStalkRing B p) ((presheaf k B 2).stalk p) := sm.toSMul
  let ell := AffineTopDifferentialFrame.determinantEquiv
    (KaehlerLocalizedFrame.localizedFrame k B (originalStalkRing B p)
      p.asIdeal.primeCompl bB)
  let t := (comparisonLinearIsoOfBasis k B p bB).trans ell
  let s := SchemeExteriorPower.wedge (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) 2 cT.openSet
    (fun i => (baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d (StructureSheaf.toOpen A cT.openSet (v i)))
  let z := (relativeDifferentialExterior (Spec.map (CommRingCat.ofHom (algebraMap k B))) 2).val.map (homOfLE hST).op
    (imageSection (Spec.map (CommRingCat.ofHom (algebraMap k A))) (Spec.map (CommRingCat.ofHom (algebraMap k B))) (Spec.map (CommRingCat.ofHom φ)) hφ cT.openSet s)
  let w : Fin 2 → originalStalkRing B p := fun i => StructureSheaf.toStalk B p (φ (v i))
  have hw : ∀ i, w i ∈ IsLocalRing.maximalIdeal (originalStalkRing B p) := by
    intro i
    have he := AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom φ) p (v i)
    rw [show w i = ((Spec.map (CommRingCat.ofHom φ))).stalkMap p
      (StructureSheaf.toStalk A (((Spec.map (CommRingCat.ofHom φ))).base p) (v i)) from he.symm]
    exact map_nonunit (((Spec.map (CommRingCat.ofHom φ))).stalkMap p).hom _ (hv i)
  have heta : (fun i => KaehlerDifferential.D k (originalStalkRing B p) (w i)) =
      ![KaehlerDifferential.D k (originalStalkRing B p) (w 0),
        KaehlerDifferential.D k (originalStalkRing B p) (w 1)] := by
    funext i
    fin_cases i <;> rfl
  have hz : t ((presheaf k B 2).germ cS.openSet p hpS z) ∈
      IsLocalRing.maximalIdeal (originalStalkRing B p) := by
    change ell (comparisonLinearIsoOfBasis k B p bB
      ((presheaf k B 2).germ cS.openSet p hpS z)) ∈ _
    rw [comparisonLinearIsoOfBasis_apply,
      AffineSpecDifferentialImageStalk.comparison_imageSection_wedge_d]
    change ell (exteriorPower.ιMulti (originalStalkRing B p) 2
      (fun i => KaehlerDifferential.D k (originalStalkRing B p) (w i))) ∈ _
    rw [heta]
    exact KltDP.RingTheory.DerivationCommonFactorWedge.coefficient_mem_maximalIdeal
      (KaehlerDifferential.D k (originalStalkRing B p)) ell.toLinearMap
      (w 0) (w 1) (hw 0) (hw 1)
  have hcoord := AffineDifferentialCartierFrameStalk.coordinate_germ_eq_coefficient_mul_frame
    k B p bB DS eS cS hpS z t
  rw [hcoord] at hz
  have hframe := AffineDifferentialCartierFrameStalk.coordinate_frame_isUnit
    k B p bB DS eS cS hpS t
  have hcoeff := mem_of_mul_unit hframe hz
  have ha := AffineDifferentialParameterCoefficientUnit.sectionCoefficient_wedge_isUnit
    k A (((Spec.map (CommRingCat.ofHom φ))).base p) bA DT eT cT (hST hpS) v bₚ hbₚ
  have hunit := ha.map (((Spec.map (CommRingCat.ofHom φ))).stalkMap p).hom
  rw [germ_appLE (Spec.map (CommRingCat.ofHom φ)) cT.openSet cS.openSet hST p hpS] at hunit
  have hmul := congrArg ((Spec (CommRingCat.of B)).presheaf.germ cS.openSet p hpS)
    (sectionCoefficient_image (Spec.map (CommRingCat.ofHom (algebraMap k A))) (Spec.map (CommRingCat.ofHom (algebraMap k B))) (Spec.map (CommRingCat.ofHom φ)) hφ DT DS eT eS cT cS hST s)
  rw [map_mul] at hmul
  rw [hmul] at hcoeff
  exact mem_of_unit_mul hunit hcoeff

end KltDP.Geometry.AffineDifferentialCartierCoefficientMaximalIdeal

#check @KltDP.Geometry.AffineDifferentialCartierCoefficientMaximalIdeal.sectionCoefficient_image_frame_mem_maximalIdeal
#print axioms KltDP.Geometry.AffineDifferentialCartierCoefficientMaximalIdeal.sectionCoefficient_image_frame_mem_maximalIdeal
