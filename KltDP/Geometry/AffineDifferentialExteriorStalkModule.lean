import KltDP.Geometry.AffineTildeOriginalStalkModule
import KltDP.Geometry.AffineDifferentialExteriorOriginalStalk

/-!
# The genuine original stalk action on the intrinsic affine exterior

The original affine exterior sheaf isomorphism transports the certified
tilde stalk action. Its compatibility with the original section action is
proved on all germs, not assumed. No native differential-stalk comparison
is used to define this action.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorOriginalStalk

open AffineKaehlerTildeDerivation
open AffineDifferentialExteriorStalkEvaluation (originalStalkRing stalkAffineAlgebra)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- Evaluate categorical naturality through the explicit ModuleCat linear map.
-- This keeps the concrete-category carrier inference out of specialization.
private theorem moduleStalkMap_germ
    (A : Type u) [CommRing A] {X : TopCat.{u}}
    {F G : X.Presheaf (ModuleCat.{u} A)} (f : F ⟶ G)
    (p : X) (U : Opens X) (hp : p ∈ U) (s : F.obj (op U)) :
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A) p).map f).hom
        ((F.germ U p hp).hom s) =
      (G.germ U p hp).hom ((f.app (op U)).hom s) := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun g : F.obj (op U) ⟶ G.stalk p => g.hom s)
      (TopCat.Presheaf.stalkFunctor_map_germ U p hp f)

-- The two actual scalar restrictions preserve the original section map.
-- Prove this before introducing any stalk or the concrete exterior inverse.
private theorem modulePresheafFunctor_map_apply
    (A : Type u) [CommRing A] {F G : (Spec (CommRingCat.of A)).Modules}
    (f : F ⟶ G) (U : Opens (PrimeSpectrum A)) (s : F.val.obj (op U)) :
    (((AffineKaehlerStalkLocalization.modulePresheafFunctor A).map f).app (op U)).hom s =
      (f.val.app (op U)).hom s := rfl

-- Compare the original germ morphisms with their source and target fixed.
-- Rewriting the entire presheaf would change the type of its section argument.
private theorem modulePresheafFunctor_tilde_germ
    (A : Type u) [CommRing A] (M : ModuleCat.{u} A)
    (p : PrimeSpectrum A) (U : Opens (PrimeSpectrum A)) (hp : p ∈ U) :
    ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).obj M.tilde).germ U p hp =
      M.tildeInModuleCat.germ U p hp := rfl

-- Combine the two opaque equalities only after the original section map has
-- been isolated from the scalar-restriction functor.
private theorem moduleToTilde_stalkMap_germ
    (A : Type u) [CommRing A] (F : (Spec (CommRingCat.of A)).Modules)
    (M : ModuleCat.{u} A) (f : F ⟶ M.tilde)
    (p : PrimeSpectrum A) (U : Opens (PrimeSpectrum A)) (hp : p ∈ U)
    (s : ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).obj F).obj (op U)) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
      (X := PrimeSpectrum.Top A) p).map
        ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).map f)
        (((AffineKaehlerStalkLocalization.modulePresheafFunctor A).obj F).germ U p hp s) =
      M.tildeInModuleCat.germ U p hp (f.val.app (op U) s) := by
  change ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
    (X := PrimeSpectrum.Top A) p).map
      ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).map f)).hom
        ((((AffineKaehlerStalkLocalization.modulePresheafFunctor A).obj F).germ
          U p hp).hom s) = _
  rw [moduleStalkMap_germ, modulePresheafFunctor_map_apply,
    modulePresheafFunctor_tilde_germ]
  dsimp only [ModuleCat.Hom.hom]
  rfl

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (p : PrimeSpectrum A) {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential k A))

local notation "Aₚ" => originalStalkRing A p

/-- The same original native exterior module, named before local notation. -/
abbrev nativeExteriorModule (n : ℕ) : ModuleCat.{u} A :=
  (differentialModule k A).exteriorPower n

local notation "N" => nativeExteriorModule k A n

local instance originalAlgebra : Algebra A Aₚ := stalkAffineAlgebra (A := A) (p := p)
local instance originalLocalization : IsLocalization.AtPrime Aₚ p.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk A p

/-- The stalk of the original affine exterior inverse, before native evaluation. -/
def toTildeStalkIsoOfBasis : (presheaf k A n).stalk p ≅ (N).tildeInModuleCat.stalk p :=
  (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
    (X := PrimeSpectrum.Top A) p).mapIso
      ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).mapIso
        (AffineDifferentialExteriorTildeMap.isoOfBasis k A b).symm)

/-- The original sheaf inverse transports the original structure-stalk action. -/
abbrev stalkModuleOfBasis : Module Aₚ ((presheaf k A n).stalk p) := by
  letI tm := AffineTildeOriginalStalk.stalkModule A p N
  letI : SMul Aₚ ((N).tildeInModuleCat.stalk p) := tm.toSMul
  exact (toTildeStalkIsoOfBasis k A p b).toLinearEquiv.toAddEquiv.module Aₚ

theorem stalkTowerOfBasis :
    letI sm := stalkModuleOfBasis k A p b
    letI : SMul Aₚ ((presheaf k A n).stalk p) := sm.toSMul
    IsScalarTower A Aₚ ((presheaf k A n).stalk p) := by
  letI tm := AffineTildeOriginalStalk.stalkModule A p N
  letI : SMul Aₚ ((N).tildeInModuleCat.stalk p) := tm.toSMul
  letI := AffineTildeOriginalStalk.stalkTower A p N
  letI sm := stalkModuleOfBasis k A p b
  letI : SMul Aₚ ((presheaf k A n).stalk p) := sm.toSMul
  exact (toTildeStalkIsoOfBasis k A p b).toLinearEquiv.isScalarTower Aₚ

/-- Localization upgrades the same stalk of the original sheaf inverse. -/
def toTildeStalkLinearIsoOfBasis :
    letI tm := AffineTildeOriginalStalk.stalkModule A p N
    letI : SMul Aₚ ((N).tildeInModuleCat.stalk p) := tm.toSMul
    letI sm := stalkModuleOfBasis k A p b
    letI : SMul Aₚ ((presheaf k A n).stalk p) := sm.toSMul
    ((presheaf k A n).stalk p) ≃ₗ[Aₚ] (N).tildeInModuleCat.stalk p := by
  letI tm := AffineTildeOriginalStalk.stalkModule A p N
  letI : SMul Aₚ ((N).tildeInModuleCat.stalk p) := tm.toSMul
  letI := AffineTildeOriginalStalk.stalkTower A p N
  letI sm := stalkModuleOfBasis k A p b
  letI : SMul Aₚ ((presheaf k A n).stalk p) := sm.toSMul
  letI := stalkTowerOfBasis k A p b
  exact (toTildeStalkIsoOfBasis k A p b).toLinearEquiv.extendScalarsOfIsLocalization
    p.asIdeal.primeCompl Aₚ

/-- The original inverse on sections induces the same map on every germ. -/
theorem toTildeStalkLinearIsoOfBasis_germ (U : Opens (PrimeSpectrum A)) (hp : p ∈ U)
    (s : (presheaf k A n).obj (op U)) :
    letI tm := AffineTildeOriginalStalk.stalkModule A p N
    letI : SMul Aₚ ((N).tildeInModuleCat.stalk p) := tm.toSMul
    letI sm := stalkModuleOfBasis k A p b
    letI : SMul Aₚ ((presheaf k A n).stalk p) := sm.toSMul
    toTildeStalkLinearIsoOfBasis k A p b ((presheaf k A n).germ U p hp s) =
      (N).tildeInModuleCat.germ U p hp
        ((AffineDifferentialExteriorTildeMap.inverseOfBasis k A b).val.app (op U) s) := by
  letI tm := AffineTildeOriginalStalk.stalkModule A p N
  letI : SMul Aₚ ((N).tildeInModuleCat.stalk p) := tm.toSMul
  letI sm := stalkModuleOfBasis k A p b
  letI : SMul Aₚ ((presheaf k A n).stalk p) := sm.toSMul
  change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} A)
    (X := PrimeSpectrum.Top A) p).map
      ((AffineKaehlerStalkLocalization.modulePresheafFunctor A).map
        (AffineDifferentialExteriorTildeMap.inverseOfBasis k A b))
      ((presheaf k A n).germ U p hp s) = _
  exact moduleToTilde_stalkMap_germ A
    (SchemeExteriorPower.sheaf (SchemeKaehlerSheaf.baseRingSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n) N
    (AffineDifferentialExteriorTildeMap.inverseOfBasis k A b) p U hp s

/-- The original intrinsic sheaf section action on the same affine-ring carrier. -/
abbrev intrinsicSectionModule (n : ℕ) (U : Opens (PrimeSpectrum A)) :
    Module Γ(Spec (CommRingCat.of A), U) ((presheaf k A n).obj (op U)) :=
  inferInstanceAs (Module ((Spec (CommRingCat.of A)).ringCatSheaf.val.obj (op U))
    ((SchemeExteriorPower.sheaf (SchemeKaehlerSheaf.baseRingSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))) n).val.obj (op U)))

/-- The transported action agrees with the original intrinsic sheaf
action on every germ, certifying the original stalk module structure. -/
theorem stalkModuleOfBasis_germ_smul (U : Opens (PrimeSpectrum A)) (hp : p ∈ U)
    (r : Γ(Spec (CommRingCat.of A), U)) (s : (presheaf k A n).obj (op U)) :
    letI um := intrinsicSectionModule k A n U
    letI : SMul Γ(Spec (CommRingCat.of A), U) ((presheaf k A n).obj (op U)) := um.toSMul
    letI sm := stalkModuleOfBasis k A p b
    letI : SMul Aₚ ((presheaf k A n).stalk p) := sm.toSMul
    (presheaf k A n).germ U p hp (r • s) =
      ((Spec (CommRingCat.of A)).presheaf.germ U p hp r) •
        (presheaf k A n).germ U p hp s := by
  letI um := intrinsicSectionModule k A n U
  letI : SMul Γ(Spec (CommRingCat.of A), U) ((presheaf k A n).obj (op U)) := um.toSMul
  letI vm := AffineTildeOriginalStalk.sectionModule A N U
  letI : SMul Γ(Spec (CommRingCat.of A), U) ((N).tildeInModuleCat.obj (op U)) := vm.toSMul
  letI tm := AffineTildeOriginalStalk.stalkModule A p N
  letI : SMul Aₚ ((N).tildeInModuleCat.stalk p) := tm.toSMul
  letI sm := stalkModuleOfBasis k A p b
  letI : SMul Aₚ ((presheaf k A n).stalk p) := sm.toSMul
  apply (toTildeStalkLinearIsoOfBasis k A p b).injective
  rw [(toTildeStalkLinearIsoOfBasis k A p b).map_smul,
    toTildeStalkLinearIsoOfBasis_germ, toTildeStalkLinearIsoOfBasis_germ,
    map_smul]
  exact AffineTildeOriginalStalk.germ_smul A p N U hp r
    ((AffineDifferentialExteriorTildeMap.inverseOfBasis k A b).val.app (op U) s)

end KltDP.Geometry.AffineDifferentialExteriorOriginalStalk
