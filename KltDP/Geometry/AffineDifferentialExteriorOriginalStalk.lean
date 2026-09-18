import KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation
import KltDP.Geometry.AffineDifferentialExteriorTildeIso
import KltDP.Geometry.AffineKaehlerStalkLocalization

/-!
# The original intrinsic differential exterior at an affine stalk

Compose the already proved native/intrinsic inverse, the pinned tilde
stalk map and the canonical native exterior localization evaluation.
The formula on germs retains the original affine coordinate derivatives.
A genuine finite differential basis supplies the inverse; for a standard
smooth surface the existing construction derives that basis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorOriginalStalk

open SchemeKaehlerSheaf AffineKaehlerTildeDerivation
open AffineDifferentialExteriorStalkEvaluation (stalkAffineAlgebra stalkGroundAlgebra stalkExteriorModule)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
  (p : PrimeSpectrum A)

local notation "Aₚ" => AffineDifferentialExteriorStalkEvaluation.originalStalkRing A p
local notation "Ωₚ" => (KaehlerDifferential k Aₚ)

/-- The original intrinsic exterior sheaf with its original affine-ring action. -/
abbrev presheaf (n : ℕ) :
    TopCat.Presheaf (ModuleCat.{u} A) (PrimeSpectrum.Top A) :=
  (AffineKaehlerStalkLocalization.modulePresheafFunctor A).obj
    (SchemeExteriorPower.sheaf
      (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n)

variable {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential k A))

/-- This map uses the actual already normalized affine inverse. -/
def comparisonOfBasis :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    (presheaf k A n).stalk p ⟶ ModuleCat.of A (⋀[Aₚ]^n Ωₚ) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  exact (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
    (X := PrimeSpectrum.Top A) p).map
      ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).map
        (AffineDifferentialExteriorTildeMap.inverseOfBasis k A b)) ≫
    AffineDifferentialExteriorStalkEvaluation.stalkMap k A p n

/-- Original intrinsic differential germs become native wedges of the
same original functions in the original structure stalk. -/
theorem comparisonOfBasis_germ_wedge_D (U : Opens (PrimeSpectrum A))
    (hp : p ∈ U) (v : Fin n → A) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    comparisonOfBasis k A p b ((presheaf k A n).germ U p hp
      (SchemeExteriorPower.wedge
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n U
        (fun i => (baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
            (StructureSheaf.toOpen A U (v i))))) =
      exteriorPower.ιMulti Aₚ n
        (fun i => KaehlerDifferential.D k Aₚ (StructureSheaf.toStalk A p (v i))) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  change AffineDifferentialExteriorStalkEvaluation.stalkMap k A p n
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
      (X := PrimeSpectrum.Top A) p).map
        ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).map
          (AffineDifferentialExteriorTildeMap.inverseOfBasis k A b)) _) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change AffineDifferentialExteriorStalkEvaluation.stalkMap k A p n
    ((((differentialModule k A).exteriorPower n).tildeInModuleCat).germ U p hp
      ((AffineDifferentialExteriorTildeMap.inverseOfBasis k A b).val.app (op U) _)) = _
  rw [AffineDifferentialExteriorTildeMap.inverseOfBasis_wedge_D]
  exact (AffineDifferentialExteriorStalkEvaluation.stalkMap_germ_toOpen k A p n U hp
    (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (v i)))).trans
      (AffineDifferentialExteriorStalkEvaluation.nativeMap_D k A p n v)

/-- Standard smoothness supplies the existing actual rank-two differential basis. -/
def standardSmoothComparison [Algebra.IsStandardSmoothOfRelativeDimension 2 k A] :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p 2
    (presheaf k A 2).stalk p ⟶ ModuleCat.of A (⋀[Aₚ]^2 Ωₚ) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p 2
  exact comparisonOfBasis k A p
    (AffineTopDifferentialFrame.standardSmoothDifferentialBasis k A)

theorem standardSmoothComparison_germ_wedge_D
    [Algebra.IsStandardSmoothOfRelativeDimension 2 k A]
    (U : Opens (PrimeSpectrum A)) (hp : p ∈ U) (v : Fin 2 → A) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p 2
    standardSmoothComparison k A p ((presheaf k A 2).germ U p hp
      (SchemeExteriorPower.wedge
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap k A)))) 2 U
        (fun i => (baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap k A)))).d
            (StructureSheaf.toOpen A U (v i))))) =
      exteriorPower.ιMulti Aₚ 2
        (fun i => KaehlerDifferential.D k Aₚ (StructureSheaf.toStalk A p (v i))) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p 2
  exact comparisonOfBasis_germ_wedge_D k A p
    (AffineTopDifferentialFrame.standardSmoothDifferentialBasis k A) U hp v

end KltDP.Geometry.AffineDifferentialExteriorOriginalStalk

#check @KltDP.Geometry.AffineDifferentialExteriorOriginalStalk.comparisonOfBasis_germ_wedge_D
#print axioms KltDP.Geometry.AffineDifferentialExteriorOriginalStalk.standardSmoothComparison_germ_wedge_D
