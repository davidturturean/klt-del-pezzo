import KltDP.Geometry.AffineStalkKaehlerLocalization
import KltDP.LinearAlgebra.ExteriorPowerScalarMap
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Native exterior forms evaluated at the original affine stalk

The original affine-to-stalk Kähler map induces the existing exterior
scalar map. Pinned module localization extends it to the original tilde
stalk. Its normalization retains each original differential and the
literal `StructureSheaf.toStalk` map. No inverse or basis is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation

open IntrinsicNodal AffineKaehlerTildeDerivation

/-- Name the existing exterior scalar action before specializing its carriers. -/
private abbrev nativeExteriorModule (R S T : Type u) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (n : ℕ) : Module S (⋀[T]^n (KaehlerDifferential R T)) := by
  letI : Module S (KaehlerDifferential R T) :=
    KaehlerDifferential.module' (R := R) (S := T) (R' := S)
  letI : IsScalarTower S T (KaehlerDifferential R T) :=
    KaehlerDifferential.isScalarTower_of_tower (R := R) (S := T) (R₁ := S) (R₂ := T)
  exact Submodule.module' (⋀[T]^n (KaehlerDifferential R T))

private def nativeExteriorTower (R S T : Type u) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (n : ℕ) :
    letI := nativeExteriorModule R S T n
    IsScalarTower S T (⋀[T]^n (KaehlerDifferential R T)) := by
  letI : Module S (KaehlerDifferential R T) :=
    KaehlerDifferential.module' (R := R) (S := T) (R' := S)
  letI : IsScalarTower S T (KaehlerDifferential R T) :=
    KaehlerDifferential.isScalarTower_of_tower (R := R) (S := T) (R₁ := S) (R₂ := T)
  letI := nativeExteriorModule R S T n
  exact Submodule.isScalarTower (⋀[T]^n (KaehlerDifferential R T))

/-- The same original affine structure stalk, named before local notation. -/
abbrev originalStalkRing (A : Type u) [CommRing A] (p : PrimeSpectrum A) : CommRingCat.{u} :=
  (Spec (CommRingCat.of A)).presheaf.stalk p

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
  (p : PrimeSpectrum A)

local notation "Aₚ" => originalStalkRing A p
local notation "Ωₚ" => (KaehlerDifferential k Aₚ)

/-- Keep the actual affine action explicit, without registering a polymorphic instance. -/
abbrev stalkAffineAlgebra : Algebra A Aₚ :=
  (StructureSheaf.toStalk A p).hom.toAlgebra

/-- The original ground action is supplied monomorphically at every use. -/
abbrev stalkGroundAlgebra : Algebra k Aₚ :=
  stalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A))) p

def stalkScalarTower :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    IsScalarTower k A Aₚ := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  exact IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun a : CommRingCat.of k ⟶ Aₚ => a.hom r)
      (AffineStalkKaehlerLocalization.scalar_map k A p)

/-- The existing native exterior module restricted through the original affine action. -/
abbrev stalkExteriorModule (n : ℕ) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    Module A (⋀[Aₚ]^n Ωₚ) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkScalarTower (k := k) (A := A) (p := p)
  exact nativeExteriorModule k A Aₚ n

def stalkExteriorTower (n : ℕ) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI exteriorModule : Module A (⋀[Aₚ]^n Ωₚ) := stalkExteriorModule k A p n
    letI : SMul A (⋀[Aₚ]^n Ωₚ) := exteriorModule.toSMul
    IsScalarTower A Aₚ (⋀[Aₚ]^n Ωₚ) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkScalarTower (k := k) (A := A) (p := p)
  letI exteriorModule : Module A (⋀[Aₚ]^n Ωₚ) := stalkExteriorModule k A p n
  letI : SMul A (⋀[Aₚ]^n Ωₚ) := exteriorModule.toSMul
  exact nativeExteriorTower k A Aₚ n

/-- Exterior scalar extension of the original affine-to-stalk Kähler map. -/
def nativeMap (n : ℕ) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    (⋀[A]^n (KaehlerDifferential k A)) →ₗ[A] (⋀[Aₚ]^n Ωₚ) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  letI := stalkScalarTower (k := k) (A := A) (p := p)
  letI : Module A Ωₚ :=
    KaehlerDifferential.module' (R := k) (S := Aₚ) (R' := A)
  letI : IsScalarTower A Aₚ Ωₚ :=
    KaehlerDifferential.isScalarTower_of_tower (R := k) (S := Aₚ) (R₁ := A) (R₂ := Aₚ)
  exact KltDP.LinearAlgebra.ExteriorPowerScalarMap.map A Aₚ n
    (KaehlerDifferential.map k k A Aₚ)

theorem nativeMap_D (n : ℕ) (v : Fin n → A) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    nativeMap k A p n
        (exteriorPower.ιMulti A n (fun i => KaehlerDifferential.D k A (v i))) =
      exteriorPower.ιMulti Aₚ n
        (fun i => KaehlerDifferential.D k Aₚ (StructureSheaf.toStalk A p (v i))) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  letI := stalkScalarTower (k := k) (A := A) (p := p)
  letI : Module A Ωₚ :=
    KaehlerDifferential.module' (R := k) (S := Aₚ) (R' := A)
  letI : IsScalarTower A Aₚ Ωₚ :=
    KaehlerDifferential.isScalarTower_of_tower (R := k) (S := Aₚ) (R₁ := A) (R₂ := Aₚ)
  rw [nativeMap, KltDP.LinearAlgebra.ExteriorPowerScalarMap.map_ιMulti]
  apply congrArg (exteriorPower.ιMulti Aₚ n)
  funext i
  exact KaehlerDifferential.map_D k k A Aₚ (v i)

private theorem denominator_units (n : ℕ) (s : p.asIdeal.primeCompl) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    IsUnit (algebraMap A (Module.End A (⋀[Aₚ]^n Ωₚ)) s) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  letI := stalkExteriorTower k A p n
  letI : IsLocalization.AtPrime Aₚ p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A p
  rw [← (Algebra.lsmul A (A := Aₚ) A (⋀[Aₚ]^n Ωₚ)).commutes]
  exact (IsLocalization.map_units Aₚ s).map _

/-- The pinned localization lift of this same original exterior map. -/
def localizedMap (n : ℕ) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    LocalizedModule p.asIdeal.primeCompl ((differentialModule k A).exteriorPower n)
      →ₗ[A] (⋀[Aₚ]^n Ωₚ) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  exact LocalizedModule.lift p.asIdeal.primeCompl
    (nativeMap k A p n) (denominator_units k A p n)

theorem localizedMap_mk_one (n : ℕ) (m : (differentialModule k A).exteriorPower n) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    localizedMap k A p n (LocalizedModule.mk m 1) = nativeMap k A p n m := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  exact LocalizedModule.lift_mk_one p.asIdeal.primeCompl
    (nativeMap k A p n) (denominator_units k A p n) m

/-- Evaluation of the original native exterior tilde stalk in the original
structure-stalk differential exterior. -/
def stalkMap (n : ℕ) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    (((differentialModule k A).exteriorPower n).tildeInModuleCat).stalk p ⟶
      ModuleCat.of A (⋀[Aₚ]^n Ωₚ) := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  exact ModuleCat.Tilde.stalkToFiberLinearMap ((differentialModule k A).exteriorPower n) p ≫
    ModuleCat.ofHom (localizedMap k A p n)

theorem stalkMap_germ_toOpen (n : ℕ) (U : Opens (PrimeSpectrum A)) (hp : p ∈ U)
    (m : (differentialModule k A).exteriorPower n) :
    letI := stalkAffineAlgebra (A := A) (p := p)
    letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
    letI := stalkExteriorModule k A p n
    stalkMap k A p n
        ((((differentialModule k A).exteriorPower n).tildeInModuleCat).germ U p hp
          (ModuleCat.Tilde.toOpen ((differentialModule k A).exteriorPower n) U m)) =
      nativeMap k A p n m := by
  letI := stalkAffineAlgebra (A := A) (p := p)
  letI := stalkGroundAlgebra (k := k) (A := A) (p := p)
  letI := stalkExteriorModule k A p n
  change localizedMap k A p n
    ((ModuleCat.Tilde.stalkToFiberLinearMap
      ((differentialModule k A).exteriorPower n) p).hom _) = _
  rw [ModuleCat.Tilde.stalkToFiberLinearMap_germ]
  change localizedMap k A p n (LocalizedModule.mk m 1) = _
  exact localizedMap_mk_one k A p n m

end KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation

#check @KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation.stalkMap_germ_toOpen
#print axioms KltDP.Geometry.AffineDifferentialExteriorStalkEvaluation.stalkMap_germ_toOpen
