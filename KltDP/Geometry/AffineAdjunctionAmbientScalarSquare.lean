import KltDP.Geometry.AffineDifferentialExteriorPullbackComparison
import KltDP.RingTheory.SmoothPrincipalTopFormRestriction

/-!
# The original ambient top-form map in the original quotient scalar square

The existing scalar-extension composition sends the original unit tensor
to the iterated unit tensor. The original quotient top-form map and the
original native exterior restriction have the same value on every wedge.
This identifies the actual module maps around the original quotient square,
before transporting that square through the affine tilde comparisons.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u
namespace KltDP.Geometry.AffineAdjunctionAmbientScalarSquare

open KltDP.RingTheory.SmoothPrincipalDeterminantRestriction
open KltDP.RingTheory.SmoothPrincipalTopFormRestriction
open AffineModuleTildeSemilinearMap AffineDifferentialExteriorPullbackComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem transport_one_tmul {A B : Type u} [CommRing A] [CommRing B]
    {φ ψ : A →+* B} (h : φ = ψ) (M : ModuleCat.{u} A) (m : M) :
    (eqToIso (congrArg (fun ρ => (ModuleCat.extendScalars ρ).obj M) h)).hom
        ((1 : B) ⊗ₜ[A,φ] m) = (1 : B) ⊗ₜ[A,ψ] m := by
  cases h
  rfl

variable (R A A' : Type u) [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
  (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))

/-- The original quotient square on its original ring maps. -/
theorem quotientMap_comp_mk :
    (quotientMap A A' J J' hφ).comp (Ideal.Quotient.mk J) =
      (Ideal.Quotient.mk J').comp (algebraMap A A') := by
  ext a
  exact Ideal.quotientMap_mk (J := J) (I := J') (f := algebraMap A A') (H := hφ)

/-- The actual ambient top-form restriction is the scalar-extended native exterior map. -/
theorem scalar_square :
    (ModuleCat.extendScalarsComp (Ideal.Quotient.mk J) (quotientMap A A' J J' hφ)).hom.app
        ((AffineKaehlerTildeDerivation.differentialModule R A).exteriorPower 2) ≫
      extendHom (quotientMap A A' J J' hφ)
        (M := (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj
          ((AffineKaehlerTildeDerivation.differentialModule R A).exteriorPower 2))
        (N := (ModuleCat.extendScalars (Ideal.Quotient.mk J')).obj
          ((AffineKaehlerTildeDerivation.differentialModule R A').exteriorPower 2))
        (ambientTopTensorMap R A A' J J' hφ) =
    (eqToIso (congrArg
      (fun ρ => (ModuleCat.extendScalars ρ).obj
        ((AffineKaehlerTildeDerivation.differentialModule R A).exteriorPower 2))
      (quotientMap_comp_mk A A' J J' hφ))).hom ≫
      (ModuleCat.extendScalarsComp (algebraMap A A') (Ideal.Quotient.mk J')).hom.app
        ((AffineKaehlerTildeDerivation.differentialModule R A).exteriorPower 2) ≫
      (ModuleCat.extendScalars (Ideal.Quotient.mk J')).map
        (extendHom (algebraMap A A') (nativeMap R A A' 2)) := by
  let M := (AffineKaehlerTildeDerivation.differentialModule R A).exteriorPower 2
  let N := (ModuleCat.extendScalars (Ideal.Quotient.mk J')).obj
    ((AffineKaehlerTildeDerivation.differentialModule R A').exteriorPower 2)
  let ψ := quotientMap A A' J J' hφ
  apply ((ModuleCat.extendRestrictScalarsAdj (ψ.comp (Ideal.Quotient.mk J))).homEquiv M N).injective
  apply ModuleCat.hom_ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change extendHom ψ (M := (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj M)
      (N := N) (ambientTopTensorMap R A A' J J' hφ)
      ((ModuleCat.extendScalarsComp (Ideal.Quotient.mk J) ψ).hom.app M
        ((1 : A' ⧸ J') ⊗ₜ[A,ψ.comp (Ideal.Quotient.mk J)] exteriorPower.ιMulti A 2 v)) =
    (ModuleCat.extendScalars (Ideal.Quotient.mk J')).map
      (extendHom (algebraMap A A') (nativeMap R A A' 2))
      ((ModuleCat.extendScalarsComp (algebraMap A A') (Ideal.Quotient.mk J')).hom.app M
        ((eqToIso (congrArg (fun ρ => (ModuleCat.extendScalars ρ).obj M)
          (quotientMap_comp_mk A A' J J' hφ))).hom
          ((1 : A' ⧸ J') ⊗ₜ[A,ψ.comp (Ideal.Quotient.mk J)] exteriorPower.ιMulti A 2 v)))
  rw [ModuleCat.extendScalarsComp_hom_app_one_tmul, extendHom_one_tmul]
  refine (ambientTopTensorMap_wedge R A A' J J' hφ (1 : A ⧸ J) (fun i => v i)).trans ?_
  rw [map_one, transport_one_tmul (quotientMap_comp_mk A A' J J' hφ) M
    (exteriorPower.ιMulti A 2 v), ModuleCat.extendScalarsComp_hom_app_one_tmul,
    ModuleCat.ExtendScalars.map_tmul, extendHom_one_tmul, nativeMap]
  exact congrArg (fun z : ⋀[A']^2 (KaehlerDifferential R A') => (1 : A' ⧸ J') ⊗ₜ[A'] z)
    (KltDP.LinearAlgebra.ExteriorPowerSemilinearMap.map_ιMulti (algebraMap A A') 2
      (AffineKaehlerPullbackComparison.differentialMap R A A') v).symm

end KltDP.Geometry.AffineAdjunctionAmbientScalarSquare
