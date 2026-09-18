import KltDP.Geometry.QuadraticOriginalBranchCanonicalChart
import KltDP.Geometry.QuadraticUnitIntrinsicCanonicalFactor

/-!
# The original global canonical factor on actual off-branch coefficient charts

The actual factor and its normalization are stored together. The factor
retains its original basis-only telescope; standard smoothness is needed
only for the normalization, exactly as in the original public theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover AffineNativeTopDifferential
open SchemeTopDifferentialFactorSquare

local instance originalUnitChartModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u}
  (D : QuadraticCoverAtlas.Data X ι) (f : X ⟶ Spec (CommRingCat.of k))
  {i : ι} (U : X.affineOpens) (hi : U.1 ≤ D.opens i)
  (h2 : IsUnit (2 : Γ(X, U.1))) (hs : IsUnit (res X hi (D.sections i)))

set_option maxHeartbeats 800000 in
/-- The original factor is paired with its original smooth normalization;
the factor itself still requires only the given actual differential basis. -/
def originalUnitCanonicalChartFactorData :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ (b : Basis (Fin 2) Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1))),
      {F : (schemeModulePullback (D.frameGlobalι hi)).obj
          ((schemeModulePullback D.morphism).obj (top f 2)) ≅
        (schemeModulePullback (D.frameGlobalι hi)).obj
          (schemeKernelIdeal D.rootZeroGlobalι ⊗ top (D.morphism ≫ f) 2) //
        ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1)],
          F.hom ≫ (schemeModulePullback (D.frameGlobalι hi)).map
            (schemeStructureTensorInclusion (schemeKernelIdealι D.rootZeroGlobalι)
              (top (D.morphism ≫ f) 2)) =
            (schemeModulePullback (D.frameGlobalι hi)).map
              (SchemeKaehlerExteriorPullbackTransport.map f D.morphism (D.morphism ≫ f) rfl 2)} := by
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro b
  letI := D.frameGlobalι_isOpenImmersion hi U.2
  let s := res X hi (D.sections i)
  let p := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U.1)))
  let q := Spec.map (CommRingCat.ofHom (algebraMap k (CoverAlgebra s)))
  refine ⟨SchemeTopDifferentialFactorSquare.factorIso f D.morphism (D.frameGlobalι hi)
    U.2.fromSpec (toBase s) (D.frameGlobalι_morphism hi U.2) (D.morphism ≫ f)
    p (frameBase_structure f U) q (D.frameGlobalι_structure f U hi) 2
    (D.rootIdealTildePullbackIso hi U.2 hs.mem_nonZeroDivisors)
    (unitIntrinsicCanonicalIso k Γ(X, U.1) s h2 hs b), ?_⟩
  intro _
  exact (SchemeTopDifferentialFactorSquare.normalizedFactor f D.morphism (D.frameGlobalι hi)
    U.2.fromSpec (toBase s) (D.frameGlobalι_morphism hi U.2)
    (D.morphism ≫ f) rfl p (frameBase_structure f U) q (D.frameGlobalι_structure f U hi)
    (spec_comp k (IsScalarTower.toAlgHom k Γ(X, U.1) (CoverAlgebra s))) 2
    (schemeKernelIdealι D.rootZeroGlobalι) (AffinePrincipalIdealTildeFrame.inclusion (rootIdeal s))
    (D.rootIdealTildePullbackIso hi U.2 hs.mem_nonZeroDivisors)
    (D.rootIdealTildePullbackIso_inclusion hi U.2 hs.mem_nonZeroDivisors)
    (unitIntrinsicCanonicalIso k Γ(X, U.1) s h2 hs b)
    (unitIntrinsicCanonicalIso_structure_factor k Γ(X, U.1) s h2 hs b)).property

/-- The off-branch factor retains the actual global sheaves and original chart. -/
def originalUnitCanonicalChartFactor :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ (b : Basis (Fin 2) Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1))),
      (schemeModulePullback (D.frameGlobalι hi)).obj
          ((schemeModulePullback D.morphism).obj (top f 2)) ≅
        (schemeModulePullback (D.frameGlobalι hi)).obj
          (schemeKernelIdeal D.rootZeroGlobalι ⊗ top (D.morphism ≫ f) 2) := by
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro b
  exact (D.originalUnitCanonicalChartFactorData f U hi h2 hs b).val

/-- The off-branch factor is normalized by the whole original global differential. -/
theorem originalUnitCanonicalChartFactor_comp :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1)]
      (b : Basis (Fin 2) Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1))),
      (D.originalUnitCanonicalChartFactor f U hi h2 hs b).hom ≫
        (schemeModulePullback (D.frameGlobalι hi)).map
          (schemeStructureTensorInclusion (schemeKernelIdealι D.rootZeroGlobalι)
            (top (D.morphism ≫ f) 2)) =
        (schemeModulePullback (D.frameGlobalι hi)).map
          (SchemeKaehlerExteriorPullbackTransport.map f D.morphism (D.morphism ≫ f) rfl 2) := by
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ b
  exact (D.originalUnitCanonicalChartFactorData f U hi h2 hs b).property

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.originalUnitCanonicalChartFactor_comp
