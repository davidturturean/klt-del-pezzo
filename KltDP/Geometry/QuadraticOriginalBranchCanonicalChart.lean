import KltDP.Geometry.QuadraticIntrinsicStructureFactor
import KltDP.Geometry.QuadraticOriginalRootKernelPullback
import KltDP.Geometry.GluedChartKaehlerPullback
import KltDP.Geometry.SchemeTopDifferentialNormalizedFactor

/-!
# The normalized canonical factor on an original quadratic branch chart

The actual affine section algebra comes from the original structure map.
The original root-ideal comparison and the proved quadratic intrinsic
factor are transported across the original chart square. The resulting
isomorphism is between pullbacks of the same global sheaves and preserves
the whole original global differential map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.QuadraticCoverAtlas.Data

open TransitionUnitGluing QuadraticCover AffineNativeTopDifferential
open SchemeTopDifferentialFactorSquare

local instance originalBranchChartModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {k : Type u} [CommRing k] {X : Scheme.{u}} {ι : Type u}
  (D : QuadraticCoverAtlas.Data X ι) (f : X ⟶ Spec (CommRingCat.of k))
  {i : ι} (U : X.affineOpens) (hi : U.1 ≤ D.opens i)

/-- The original affine section algebra has exactly the original structure map. -/
theorem frameBase_structure :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    U.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U.1))) := by
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  exact (Spec_map_baseToAffineSectionsMap f U.2).symm

/-- The original cover chart has the actual induced quadratic base algebra. -/
theorem frameGlobalι_structure :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    D.frameGlobalι hi ≫ (D.morphism ≫ f) =
      Spec.map (CommRingCat.ofHom (algebraMap k (CoverAlgebra (res X hi (D.sections i))))) := by
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  rw [← Category.assoc, D.frameGlobalι_morphism hi U.2]
  change (toBase (res X hi (D.sections i)) ≫ U.2.fromSpec) ≫ f = _
  rw [Category.assoc, frameBase_structure f U]
  exact spec_comp k (IsScalarTower.toAlgHom k Γ(X, U.1)
    (CoverAlgebra (res X hi (D.sections i))))

variable (hs : res X hi (D.sections i) ∈ nonZeroDivisors Γ(X, U.1))
  (h2 : IsUnit (2 : Γ(X, U.1)))

set_option maxHeartbeats 800000 in
/-- The same original branch factor and its original normalization are
constructed together, before the public projections expose either part. -/
def originalBranchCanonicalChartFactorData :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Nontrivial Γ(X, U.1)] [Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1)]
      (b : Basis (Fin 2) Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)))
      (hb : b 0 = KaehlerDifferential.D k Γ(X, U.1) (res X hi (D.sections i))),
      {F : (schemeModulePullback (D.frameGlobalι hi)).obj
          ((schemeModulePullback D.morphism).obj (top f 2)) ≅
        (schemeModulePullback (D.frameGlobalι hi)).obj
          (schemeKernelIdeal D.rootZeroGlobalι ⊗ top (D.morphism ≫ f) 2) //
        F.hom ≫ (schemeModulePullback (D.frameGlobalι hi)).map
          (schemeStructureTensorInclusion (schemeKernelIdealι D.rootZeroGlobalι)
            (top (D.morphism ≫ f) 2)) =
          (schemeModulePullback (D.frameGlobalι hi)).map
            (SchemeKaehlerExteriorPullbackTransport.map f D.morphism (D.morphism ≫ f) rfl 2)} := by
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _ b hb
  letI := D.frameGlobalι_isOpenImmersion hi U.2
  let s := res X hi (D.sections i)
  let p := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U.1)))
  let q := Spec.map (CommRingCat.ofHom (algebraMap k (CoverAlgebra s)))
  exact SchemeTopDifferentialFactorSquare.normalizedFactor f D.morphism (D.frameGlobalι hi)
    U.2.fromSpec (toBase s) (D.frameGlobalι_morphism hi U.2)
    (D.morphism ≫ f) rfl p (frameBase_structure f U) q (D.frameGlobalι_structure f U hi)
    (spec_comp k (IsScalarTower.toAlgHom k Γ(X, U.1) (CoverAlgebra s))) 2
    (schemeKernelIdealι D.rootZeroGlobalι) (AffinePrincipalIdealTildeFrame.inclusion (rootIdeal s))
    (D.rootIdealTildePullbackIso hi U.2 hs) (D.rootIdealTildePullbackIso_inclusion hi U.2 hs)
    (branchIntrinsicCanonicalIso k Γ(X, U.1) s hs h2 b hb)
    (branchIntrinsicCanonicalIso_structure_factor k Γ(X, U.1) s hs h2 b hb)

/-- The local branch factor concerns the original global source and target
sheaves, using the original chart and the actual global ramification ideal. -/
def originalBranchCanonicalChartFactor :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Nontrivial Γ(X, U.1)] [Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1)]
      (b : Basis (Fin 2) Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)))
      (hb : b 0 = KaehlerDifferential.D k Γ(X, U.1) (res X hi (D.sections i))),
      (schemeModulePullback (D.frameGlobalι hi)).obj
          ((schemeModulePullback D.morphism).obj (top f 2)) ≅
        (schemeModulePullback (D.frameGlobalι hi)).obj
          (schemeKernelIdeal D.rootZeroGlobalι ⊗ top (D.morphism ≫ f) 2) := by
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _ b hb
  exact (D.originalBranchCanonicalChartFactorData f U hi hs h2 b hb).val

/-- The normalization is the proved property of the same original factor. -/
theorem originalBranchCanonicalChartFactor_comp :
    letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Nontrivial Γ(X, U.1)] [Algebra.IsStandardSmoothOfRelativeDimension 2 k Γ(X, U.1)]
      (b : Basis (Fin 2) Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)))
      (hb : b 0 = KaehlerDifferential.D k Γ(X, U.1) (res X hi (D.sections i))),
      (D.originalBranchCanonicalChartFactor f U hi hs h2 b hb).hom ≫
        (schemeModulePullback (D.frameGlobalι hi)).map
          (schemeStructureTensorInclusion (schemeKernelIdealι D.rootZeroGlobalι)
            (top (D.morphism ≫ f) 2)) =
        (schemeModulePullback (D.frameGlobalι hi)).map
          (SchemeKaehlerExteriorPullbackTransport.map f D.morphism (D.morphism ≫ f) rfl 2) := by
  letI : Algebra k Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _ b hb
  exact (D.originalBranchCanonicalChartFactorData f U hi hs h2 b hb).property

end KltDP.Geometry.QuadraticCoverAtlas.Data

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.originalBranchCanonicalChartFactor_comp
