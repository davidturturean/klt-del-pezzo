import KltDP.Geometry.OriginalCartierQuadraticIntegral
import KltDP.Geometry.QuadraticCoverNormalBaseDimension
import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.NormalAffineSections

/-!
# Dimension two for the original cover of a normal projective surface

The actual nonempty reduced Cartier branch proves integrality of the
unchanged cover. One original affine chart has nonempty source by the
proved surjectivity of the quadratic algebra. Its coordinate ring is a
domain because it is an actual open subscheme of that same integral
cover. Normality and dimension two of the original base chart supply the
proved algebraic dimension comparison. The original open-immersion
section isomorphism identifies this chart dimension with the global
dimension of the actual cover of finite type over the original field.

No integrality, dimension, regularity, or normality of the cover is an
input. Normality and smoothness of the resulting cover remain separate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalCartierQuadraticIntegral

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem affineSource_dimension_eq_global
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    {Y : Scheme.{u}} [IsIntegral Y]
    (σ : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType σ]
    (j : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion j]
    (z : (Spec (CommRingCat.of R) : Scheme.{u})) :
    ringKrullDim R = topologicalKrullDim Y := by
  let V := j.opensRange
  letI : Nonempty V := ⟨⟨j.base z, ⟨z, rfl⟩⟩⟩
  have hV : IsAffineOpen V := isAffineOpen_opensRange j
  let e : Γ(Y, V) ≃+* R :=
    ((IsOpenImmersion.ΓIsoTop j).symm ≪≫
      Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  exact (ringKrullDim_eq_of_ringEquiv e).symm.trans
    (nonempty_affine_dimension_eq_global Y σ hV)

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance originalCartierQuadraticDimensionSeparated : S.toScheme.IsSeparated := NormalProjectiveSurface.surfaceSeparated S
local instance originalCartierQuadraticDimensionMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The same original cover has dimension two, derived from its actual reduced nonempty branch. -/
theorem dimension_two_of_reduced_nonempty_branch
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued) :
    topologicalKrullDim (InvertibleQuadraticAtlas.fromSquareRoot S.toScheme L
      (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)).scheme = 2 := by
  let A := effectiveCartierQuadraticAtlas S.toScheme E hE L e
  change topologicalKrullDim A.scheme = 2
  letI : IsIntegral A.scheme := scheme_isIntegral_of_reduced_nonempty_branch
    S.toScheme E hE L e S.normal hred hne
  letI : LocallyOfFiniteType S.structureMorphism := S.projective.locallyOfFiniteType
  letI : IsFinite A.morphism := A.morphism_isFinite
  letI : LocallyOfFiniteType (A.morphism ≫ S.structureMorphism) := inferInstance
  let x : S.toScheme := Classical.choice inferInstance
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ i, A.opens i by rw [A.covers]; trivial)
  letI : Nonempty (A.opens i) := ⟨⟨x, hi⟩⟩
  letI : IsDomain Γ(S.toScheme, A.opens i) := IsIntegral.component_integral (A.opens i)
  letI : IsIntegrallyClosed Γ(S.toScheme, A.opens i) :=
    S.affineSections_isIntegrallyClosed (A.affine i)
  letI := affineSectionsAlgebra S.structureMorphism (A.affine i)
  letI := affineSectionsAlgebra_finiteType S.structureMorphism (A.affine i)
  let s := TransitionUnitGluing.res S.toScheme (le_refl (A.opens i)) (A.sections i)
  let z : (Spec Γ(S.toScheme, A.opens i) : Scheme.{u}) := Classical.choice inferInstance
  obtain ⟨y, _hy⟩ := QuadraticCover.toBase_surjective s z
  letI : Nonempty (A.chart i) := ⟨y⟩
  letI : IsIntegral (A.chart i) := isIntegral_of_isOpenImmersion (A.chartι i)
  letI : IsDomain (QuadraticCover.CoverAlgebra s) :=
    (affine_isIntegral_iff (CommRingCat.of (QuadraticCover.CoverAlgebra s))).mp
      (inferInstanceAs (IsIntegral (A.chart i)))
  have hbase : ringKrullDim Γ(S.toScheme, A.opens i) = 2 :=
    (nonempty_affine_dimension_eq_global S.toScheme S.structureMorphism (A.affine i)).trans
      S.dimension_two
  calc
    topologicalKrullDim A.scheme = ringKrullDim (QuadraticCover.CoverAlgebra s) :=
      (affineSource_dimension_eq_global (A.morphism ≫ S.structureMorphism) (A.chartι i) y).symm
    _ = 2 := QuadraticCover.ringKrullDim_eq_of_normal k Γ(S.toScheme, A.opens i) s 2 hbase

end KltDP.Geometry.OriginalCartierQuadraticIntegral

#print axioms KltDP.Geometry.OriginalCartierQuadraticIntegral.dimension_two_of_reduced_nonempty_branch
