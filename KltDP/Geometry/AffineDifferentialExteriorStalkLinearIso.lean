import KltDP.Geometry.AffineDifferentialExteriorStalkModule
import KltDP.Geometry.AffineDifferentialExteriorStalkIso

/-!
# The original affine exterior comparison over the original stalk ring

The actual intrinsic stalk has its section-compatible original stalk action.
The actual native exterior has its original ground and stalk actions.
Pinned localization scalar extension promotes the already proved affine
isomorphism while retaining exactly its original comparison map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorOriginalStalk

open AffineDifferentialExteriorStalkEvaluation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (p : PrimeSpectrum A) {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential k A))

local notation "Aₚ" => originalStalkRing A p

/-- The original comparison is an isomorphism over the original structure stalk. -/
def comparisonLinearIsoOfBasis :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    letI := stalkModuleOfBasis k A p b
    ((presheaf k A n).stalk p) ≃ₗ[Aₚ] (⋀[Aₚ]^n (KaehlerDifferential k Aₚ)) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  letI := stalkExteriorTower k A p n
  letI := stalkModuleOfBasis k A p b
  letI := stalkTowerOfBasis k A p b
  letI : IsLocalization.AtPrime Aₚ p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A p
  exact (comparisonIsoOfBasis k A p b).toLinearEquiv.extendScalarsOfIsLocalization
    p.asIdeal.primeCompl Aₚ

/-- The underlying map remains the already normalized original comparison. -/
theorem comparisonLinearIsoOfBasis_apply (x : (presheaf k A n).stalk p) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    letI := stalkModuleOfBasis k A p b
    comparisonLinearIsoOfBasis k A p b x = comparisonOfBasis k A p b x := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  letI := stalkModuleOfBasis k A p b
  change (comparisonIsoOfBasis k A p b).hom x = comparisonOfBasis k A p b x
  exact congrArg (fun f => f x) (comparisonIsoOfBasis_hom k A p b)

/-- Original intrinsic differential germs still give the original native wedges. -/
theorem comparisonLinearIsoOfBasis_germ_wedge_D (U : Opens (PrimeSpectrum A))
    (hp : p ∈ U) (v : Fin n → A) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    letI := stalkModuleOfBasis k A p b
    comparisonLinearIsoOfBasis k A p b ((presheaf k A n).germ U p hp
      (SchemeExteriorPower.wedge
        (SchemeKaehlerSheaf.baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n U
        (fun i => (SchemeKaehlerSheaf.baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
            (StructureSheaf.toOpen A U (v i))))) =
      exteriorPower.ιMulti Aₚ n
        (fun i => KaehlerDifferential.D k Aₚ (StructureSheaf.toStalk A p (v i))) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  letI := stalkModuleOfBasis k A p b
  rw [comparisonLinearIsoOfBasis_apply]
  exact comparisonOfBasis_germ_wedge_D k A p b U hp v

/-- Original standard smoothness supplies the rank-two differential basis. -/
def standardSmoothLinearIso [Algebra.IsStandardSmoothOfRelativeDimension 2 k A] :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p 2
    letI := stalkModuleOfBasis k A p
      (AffineTopDifferentialFrame.standardSmoothDifferentialBasis k A)
    ((presheaf k A 2).stalk p) ≃ₗ[Aₚ] (⋀[Aₚ]^2 (KaehlerDifferential k Aₚ)) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p 2
  letI := stalkModuleOfBasis k A p
    (AffineTopDifferentialFrame.standardSmoothDifferentialBasis k A)
  exact comparisonLinearIsoOfBasis k A p
    (AffineTopDifferentialFrame.standardSmoothDifferentialBasis k A)

end KltDP.Geometry.AffineDifferentialExteriorOriginalStalk
