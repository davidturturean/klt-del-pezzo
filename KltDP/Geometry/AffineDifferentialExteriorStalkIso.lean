import KltDP.Geometry.AffineDifferentialExteriorStalkLocalization
import KltDP.Geometry.AffineDifferentialExteriorOriginalStalk

/-!
# Invertibility of the original intrinsic exterior stalk comparison

The pinned tilde stalk isomorphism and the proved localization isomorphism
have exactly the existing evaluation as their composite. Applying the
original presheaf and stalk functors to the already proved affine exterior
sheaf isomorphism therefore proves invertibility of the original intrinsic
comparison. The scalar ring here remains the original affine ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

namespace AffineDifferentialExteriorStalkEvaluation

open AffineKaehlerTildeDerivation

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (p : PrimeSpectrum A) {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential k A))

local notation "Aₚ" => originalStalkRing A p

/-- The original tilde stalk comparison with its proved localization inverse. -/
def nativeStalkIso :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    (((differentialModule k A).exteriorPower n).tildeInModuleCat).stalk p ≅
      ModuleCat.of A (⋀[Aₚ]^n (KaehlerDifferential k Aₚ)) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  exact ModuleCat.Tilde.stalkIso ((differentialModule k A).exteriorPower n) p ≪≫
    (localizationIso k A p b).toModuleIso

theorem nativeStalkIso_hom :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    (nativeStalkIso k A p b).hom = stalkMap k A p n := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  change ModuleCat.Tilde.stalkToFiberLinearMap
      ((differentialModule k A).exteriorPower n) p ≫
        ModuleCat.ofHom (localizationIso k A p b).toLinearMap =
    ModuleCat.Tilde.stalkToFiberLinearMap
      ((differentialModule k A).exteriorPower n) p ≫
        ModuleCat.ofHom (localizedMap k A p n)
  rw [localizedMap_eq_localizationIso k A p b]

end AffineDifferentialExteriorStalkEvaluation

namespace AffineDifferentialExteriorOriginalStalk

open AffineDifferentialExteriorStalkEvaluation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (p : PrimeSpectrum A) {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential k A))

local notation "Aₚ" => originalStalkRing A p

/-- The original affine inverse, followed by the same original native evaluation. -/
def comparisonIsoOfBasis :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    (presheaf k A n).stalk p ≅
      ModuleCat.of A (⋀[Aₚ]^n (KaehlerDifferential k Aₚ)) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  exact (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
    (X := PrimeSpectrum.Top A) p).mapIso
      ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).mapIso
        (AffineDifferentialExteriorTildeMap.isoOfBasis k A b).symm) ≪≫
    nativeStalkIso k A p b

theorem comparisonIsoOfBasis_hom :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    (comparisonIsoOfBasis k A p b).hom = comparisonOfBasis k A p b := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
      (X := PrimeSpectrum.Top A) p).map
        ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).map
          (AffineDifferentialExteriorTildeMap.inverseOfBasis k A b)) ≫
      (nativeStalkIso k A p b).hom = _
  rw [nativeStalkIso_hom]
  rfl

theorem comparisonOfBasis_isIso :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    IsIso (comparisonOfBasis k A p b) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  rw [← comparisonIsoOfBasis_hom k A p b]
  infer_instance

end AffineDifferentialExteriorOriginalStalk

end KltDP.Geometry

#check @KltDP.Geometry.AffineDifferentialExteriorOriginalStalk.comparisonOfBasis_isIso
#print axioms KltDP.Geometry.AffineDifferentialExteriorOriginalStalk.comparisonOfBasis_isIso
