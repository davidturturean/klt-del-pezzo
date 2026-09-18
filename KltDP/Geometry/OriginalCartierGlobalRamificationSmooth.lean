import KltDP.Geometry.OriginalCartierRamificationSmooth
import KltDP.Geometry.QuadraticRamificationGluing

/-!
# Smoothness of the original global root-zero subscheme

The actual global root-zero scheme and its closed immersion into the
original cover are already constructed. Its original chart triangles
transfer the proved smoothness of each original Cartier branch chart.
Source locality proves smoothness of this same global root-zero scheme
over the original field. No global branch isomorphism or new gluing is
assumed. Smoothness of the ambient cover at branch points is not asserted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierRamificationSmooth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
local instance : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

variable (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    {k : Type u} [Field k] (σ : X ⟶ Spec (CommRingCat.of k))

/-- The actual globally glued root-zero scheme of the original cover is smooth. -/
theorem globalRootZero_isSmooth
    (hsm : IsSmooth ((effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo ≫ σ)) :
    let A := effectiveCartierQuadraticAtlas X E hE L e
    IsSmooth (A.rootZeroGlobalι ≫ A.morphism ≫ σ) := by
  let A := effectiveCartierQuadraticAtlas X E hE L e
  apply IsLocalAtSource.of_openCover (P := @IsSmooth) A.rootZeroGlueData.openCover
  intro i
  change IsSmooth (A.rootZeroGlobalChartι i ≫ (A.rootZeroGlobalι ≫ A.morphism ≫ σ))
  rw [← Category.assoc, A.rootZeroGlobalChartι_globalι, Category.assoc,
    A.chartι_morphism_assoc]
  change IsSmooth (QuadraticCover.rootZeroι
    (TransitionUnitGluing.res X (le_refl (A.opens i)) (A.sections i)) ≫
      QuadraticCover.toBase
        (TransitionUnitGluing.res X (le_refl (A.opens i)) (A.sections i)) ≫
      (A.affine i).fromSpec ≫ σ)
  let P (s : Γ(X, A.opens i)) : Prop :=
    IsSmooth (QuadraticCover.rootZeroι s ≫ QuadraticCover.toBase s ≫ (A.affine i).fromSpec ≫ σ)
  exact (congrArg P (TransitionUnitGluing.res_self X (A.opens i) (A.sections i))).mpr
    (rootZeroChart_isSmooth X E hE L e σ hsm i)

end KltDP.Geometry.OriginalCartierRamificationSmooth

#print axioms KltDP.Geometry.OriginalCartierRamificationSmooth.globalRootZero_isSmooth
