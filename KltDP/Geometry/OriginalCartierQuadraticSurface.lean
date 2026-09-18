import KltDP.Geometry.OriginalCartierQuadraticNormal
import KltDP.Geometry.OriginalCartierQuadraticDimension
import KltDP.Geometry.OriginalQuadraticProjective

/-!
# The original reduced-branch cover as a normal projective surface

The same original square-root cover supplies every field of the surface
structure: the original reduced nonempty Cartier branch gives integrality
and normality, the original finite morphism gives projectivity, and the
original affine charts give dimension two. The underlying scheme and its
field morphism are definitionally the original ones used by the actual
unbranched-tree splitting construction.

No geometry of the cover is an input. Ambient smoothness at the branch
is a separate, stronger assertion than this normal surface construction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalCartierQuadraticIntegral

open InvertibleQuadraticAtlas

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance originalCartierQuadraticSurfaceSeparated : S.toScheme.IsSeparated := NormalProjectiveSurface.surfaceSeparated S
local instance originalCartierQuadraticSurfaceMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
    (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)

/-- The unchanged original cover, with its normal projective surface properties derived. -/
def normalProjectiveSurface : NormalProjectiveSurface k where
  toScheme := (fromSquareRoot S.toScheme L (cartierDivisorModule S.toScheme E) e
    (effectiveCartierSection S.toScheme E hE)).scheme
  structureMorphism := (fromSquareRoot S.toScheme L (cartierDivisorModule S.toScheme E) e
    (effectiveCartierSection S.toScheme E hE)).morphism ≫ S.structureMorphism
  integral := scheme_isIntegral_of_reduced_nonempty_branch
    S.toScheme E hE L e S.normal hred hne
  normal := by
    have h2' : IsUnit (2 : Γ(S.toScheme, ⊤)) := by
      simpa only [map_ofNat] using h2.map
        (S.structureMorphism.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
    exact scheme_isNormal_of_reduced_nonempty_branch S.toScheme E hE L e S.normal h2' hred hne
  projective := fromSquareRoot_isProjective S.toScheme L (cartierDivisorModule S.toScheme E) e
    (effectiveCartierSection S.toScheme E hE) S.structureMorphism S.projective
  dimension_two := dimension_two_of_reduced_nonempty_branch S E hE L e hred hne

@[simp] theorem normalProjectiveSurface_toScheme :
    (normalProjectiveSurface S E hE L e h2 hred hne).toScheme =
      (fromSquareRoot S.toScheme L (cartierDivisorModule S.toScheme E) e
        (effectiveCartierSection S.toScheme E hE)).scheme := rfl

@[simp] theorem normalProjectiveSurface_structureMorphism :
    (normalProjectiveSurface S E hE L e h2 hred hne).structureMorphism =
      (fromSquareRoot S.toScheme L (cartierDivisorModule S.toScheme E) e
        (effectiveCartierSection S.toScheme E hE)).morphism ≫ S.structureMorphism := rfl

end KltDP.Geometry.OriginalCartierQuadraticIntegral

#print axioms KltDP.Geometry.OriginalCartierQuadraticIntegral.normalProjectiveSurface
