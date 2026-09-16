import KltDP.Geometry.AffineModuleTildeSemilinearMap
import KltDP.RingTheory.NormalTwistedAdjunctionRestriction

/-!
# The original normal-twisted module adjunction on affine pullback sheaves

The proved original module restriction square lifts through the original
affine tilde and scalar-extension comparison. Both restriction maps retain
the original quotient differential, ambient top form, and normal-module maps.
Identifying the differential map with the original global Kähler restriction
and identifying the exterior factor remain separate global-chart adapters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace KltDP.Geometry.NormalTwistedAdjunctionTildeRestriction

open KltDP.RingTheory.SmoothPrincipalDeterminantRestriction
open KltDP.RingTheory.NormalTwistedAdjunctionRestriction
open AffineModuleTildeSemilinearMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A)

local instance twistedAddCommGroup :
    AddCommGroup (((A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A))) ⊗[A ⧸ J]
      Module.Dual (A ⧸ J) J.Cotangent) :=
  Module.addCommMonoidToAddCommGroup (A ⧸ J)

/-- The original quotient differential module. -/
abbrev differentialModule : ModuleCat.{u} (A ⧸ J) :=
  ModuleCat.of (A ⧸ J) (KaehlerDifferential R (A ⧸ J))

/-- The original ambient top-form scalar extension tensored with the actual normal module. -/
abbrev twistedModule : ModuleCat.{u} (A ⧸ J) :=
  ModuleCat.of (A ⧸ J)
    (((A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A))) ⊗[A ⧸ J]
      Module.Dual (A ⧸ J) J.Cotangent)

variable (A' : Type u) [CommRing A'] [Algebra R A'] [Algebra A A']
  [IsScalarTower R A A'] (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
  (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
  (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
  (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A')
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A']
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ J')]

/-- The original tilde adjunction square, with the actual quotient-ring pullback and
the original semilinear differential and normal-twisted restriction maps. -/
theorem iso_restriction :
    (schemeModulePullback
        (Spec.map (CommRingCat.ofHom (quotientMap A A' J J' hφ)))).map
      (AffineModuleTilde.linearEquivIso
        (M := differentialModule R A J) (N := twistedModule R A J)
        (KltDP.RingTheory.NormalTwistedAdjunction.equiv R A J d hJ hd)).hom ≫
      pullbackMap (quotientMap A A' J J' hφ)
        (M := twistedModule R A J) (N := twistedModule R A' J')
        (twistedRestriction R A A' J J' hφ d hJ hd hJ' hd') =
    pullbackMap (quotientMap A A' J J' hφ)
        (M := differentialModule R A J) (N := differentialModule R A' J')
        (quotientDifferentialMap R A A' J J' hφ) ≫
      (AffineModuleTilde.linearEquivIso
        (M := differentialModule R A' J') (N := twistedModule R A' J')
        (KltDP.RingTheory.NormalTwistedAdjunction.equiv R A' J'
          (mappedEquation A A' J J' hφ d) hJ' hd')).hom := by
  exact pullbackMap_square (quotientMap A A' J J' hφ)
    (M := differentialModule R A J) (M' := twistedModule R A J)
    (N := differentialModule R A' J') (N' := twistedModule R A' J')
    (ModuleCat.ofHom (KltDP.RingTheory.NormalTwistedAdjunction.equiv R A J d hJ hd).toLinearMap)
    (ModuleCat.ofHom (KltDP.RingTheory.NormalTwistedAdjunction.equiv R A' J'
      (mappedEquation A A' J J' hφ d) hJ' hd').toLinearMap)
    (quotientDifferentialMap R A A' J J' hφ)
    (twistedRestriction R A A' J J' hφ d hJ hd hJ' hd')
    (equiv_restriction R A A' J J' hφ d hJ hd hJ' hd')

end KltDP.Geometry.NormalTwistedAdjunctionTildeRestriction
