import KltDP.Geometry.AffineEtaleNativeDifferentialFrame
import KltDP.Geometry.StandardSmoothIdealDifferentialFactor
import KltDP.Geometry.QuadraticCoverEtale
import KltDP.Geometry.QuadraticRootIdeals

/-!
# The original quadratic canonical factor where its original coefficient is a unit

The original quadratic algebra is étale, and its root ideal is the whole
ring. The proved native étale frame gives an equivalence onto that actual
ideal whose inclusion is the original native map. The existing normalized
intrinsic comparison then supplies the same root-ideal tensor factor.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.QuadraticCover

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame
open AffineNativeTopDifferential AffineNativeTopDifferentialIdealTensor

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  (s : R) (h2 : IsUnit (2 : R)) (hs : IsUnit s)
  (b : Basis (Fin 2) R (KaehlerDifferential k R))

include hs in
/-- The original root ideal is the whole ring on the actual unit-coefficient locus. -/
theorem rootIdeal_eq_top_of_isUnit : rootIdeal s = ⊤ :=
  Ideal.span_singleton_eq_top.mpr (root_isUnit s hs)

/-- The actual original root-ideal inclusion is an equivalence on this locus. -/
def unitRootIdealEquiv : rootIdeal s ≃ₗ[CoverAlgebra s] CoverAlgebra s :=
  LinearEquiv.ofBijective (rootIdeal s).subtype
    ⟨Subtype.val_injective, fun z =>
      ⟨⟨z, by rw [rootIdeal_eq_top_of_isUnit R s hs]; trivial⟩, rfl⟩⟩

/-- The actual étale quadratic algebra carries the original differential basis. -/
def unitDifferentialBasis : Basis (Fin 2) (CoverAlgebra s) (KaehlerDifferential k (CoverAlgebra s)) := by
  letI := isStandardSmoothOfRelativeDimension_zero s h2 hs
  exact AffineEtaleNativeDifferentialFrame.basis k R (CoverAlgebra s) b

/-- The original source frame gives an equivalence onto the actual unit root ideal. -/
def unitNativeIdealEquiv :
    (ModuleCat.extendScalars (algebraMap R (CoverAlgebra s))).obj
      ((differentialModule k R).exteriorPower 2) ≃ₗ[CoverAlgebra s] rootIdeal s :=
  (extendedFrame k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b).trans
    (unitRootIdealEquiv R s hs).symm

theorem unitNativeIdealEquiv_val
    (omega : (ModuleCat.extendScalars (algebraMap R (CoverAlgebra s))).obj
      ((differentialModule k R).exteriorPower 2)) :
    (unitNativeIdealEquiv k R s hs b omega : CoverAlgebra s) =
      extendedFrame k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b omega :=
  (unitRootIdealEquiv R s hs).apply_symm_apply _

/-- The produced ideal factor is the original whole native map. -/
theorem unitNativeIdealEquiv_factor :
    (determinantEquiv (unitDifferentialBasis k R s h2 hs b)).symm.toLinearMap.comp
      ((rootIdeal s).subtype.comp (unitNativeIdealEquiv k R s hs b).toLinearMap) =
      (AffineNativeTopDifferential.map k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) 2).hom := by
  letI := isStandardSmoothOfRelativeDimension_zero s h2 hs
  apply LinearMap.ext
  intro omega
  change (determinantEquiv (unitDifferentialBasis k R s h2 hs b)).symm
    (unitNativeIdealEquiv k R s hs b omega : CoverAlgebra s) = _
  apply (determinantEquiv (unitDifferentialBasis k R s h2 hs b)).injective
  rw [LinearEquiv.apply_symm_apply, unitNativeIdealEquiv_val]
  exact (AffineEtaleNativeDifferentialFrame.map_frame k R (CoverAlgebra s) b omega).symm

local instance unitCanonicalModules : MonoidalCategory (Spec (.of (CoverAlgebra s))).Modules :=
  Scheme.Modules.monoidalCategory _

/-- The same actual intrinsic sheaves have the original root-ideal tensor factor. -/
def unitIntrinsicCanonicalIso :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap R (CoverAlgebra s))))).obj
        (intrinsic k R 2) ≅
      (ModuleCat.of (CoverAlgebra s) (rootIdeal s)).tilde ⊗ intrinsic k (CoverAlgebra s) 2 :=
  tensorIso k (CoverAlgebra s) (unitDifferentialBasis k R s h2 hs b) (rootIdeal s)
    (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b (unitNativeIdealEquiv k R s hs b)

/-- The actual tensor factor retains the original intrinsic differential map. -/
theorem unitIntrinsicCanonicalIso_factor [Algebra.IsStandardSmoothOfRelativeDimension 2 k R] :
    (unitIntrinsicCanonicalIso k R s h2 hs b).hom ≫ tensorInclusion k (CoverAlgebra s) (rootIdeal s) =
      intrinsicMap k (IsScalarTower.toAlgHom k R (CoverAlgebra s)) 2 :=
  tensorIso_factor_of_standardSmooth k (CoverAlgebra s)
    (IsScalarTower.toAlgHom k R (CoverAlgebra s)) b
    (unitDifferentialBasis k R s h2 hs b) (rootIdeal s)
    (unitNativeIdealEquiv k R s hs b) (unitNativeIdealEquiv_factor k R s h2 hs b)

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.unitIntrinsicCanonicalIso_factor
