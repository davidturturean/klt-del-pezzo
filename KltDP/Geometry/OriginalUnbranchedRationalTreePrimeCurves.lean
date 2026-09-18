import KltDP.Geometry.RationalComponentPrimeCurves
import KltDP.Geometry.UnbranchedRationalTreeAmbientComponentCopies
import KltDP.Geometry.OriginalCartierQuadraticSurface

/-!
# Actual prime-curve copies of an original unbranched rational tree

The target is the unchanged original quadratic surface. Each actual
prime curve is the closed image of the original reduced component under
the already constructed coherent whole-tree map. Original projections,
source-image comparisons, disjoint opposite sheets, and exact doubled
cardinality are proved for this same family.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

open NormalProjectiveSurface RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance originalUnbranchedTreePrimeSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedTreePrimeMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable {C : Scheme.{u}} [NoetherianSpace C] [IsLocallyNoetherian C] [IsReduced C]
    [ConnectedSpace C] [C.IsSeparated]
    (sC : C ⟶ Spec (CommRingCat.of k)) [IsProper sC]
    (hdim : topologicalKrullDim C ≤ 1)
    (hTree : (componentPointIncidenceGraph C).IsTree)
    (htrans : HasTransverseComponentBranches C)
    (eC : ∀ D : ↥(irreducibleComponents C), componentUnionScheme C {D} ≅ projectiveSpace k 1)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base))

local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "treeCopy" =>
  UnbranchedRationalTreeAmbientCopies.copy sC hdim hTree htrans eC E hE L e f hdisj h2.ne_zero

/-- The actual prime image of an original reduced component under its unchanged coherent copy. -/
def liftedCurve (ε : Bool) (D : ↥(irreducibleComponents C)) : (CoverSurface).PrimeCurve :=
  RationalComponentPrimeCurves.curve CoverSurface (treeCopy ε) eC D

/-- The unchanged coherent component map, with its domain expressed as the original prime curve. -/
def primeLift (ε : Bool) (D : ↥(irreducibleComponents C)) :
    (RationalComponentPrimeCurves.curve S f eC D).toScheme ⟶
      (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme :=
  RationalComponentPrimeCurves.liftThrough S f eC (treeCopy ε) D

instance primeLift_isClosedImmersion (ε : Bool) (D : ↥(irreducibleComponents C)) :
    IsClosedImmersion (primeLift S sC hdim hTree htrans eC E hE L e h2 f hdisj ε D) := by
  dsimp only [primeLift]
  infer_instance

@[reassoc]
theorem primeLift_projection (ε : Bool) (D : ↥(irreducibleComponents C)) :
    primeLift S sC hdim hTree htrans eC E hE L e h2 f hdisj ε D ≫
      (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism =
        (RationalComponentPrimeCurves.curve S f eC D).inclusion :=
  RationalComponentPrimeCurves.liftThrough_projection S f eC (treeCopy ε) _
    (UnbranchedRationalTreeAmbientCopies.copy_projection
      sC hdim hTree htrans eC E hE L e f hdisj h2.ne_zero ε) D

/-- Expressing the source as an original prime curve does not change its actual image. -/
theorem closedImage_primeLift (ε : Bool) (D : ↥(irreducibleComponents C)) :
    (RationalComponentPrimeCurves.curve S f eC D).closedImage (T := CoverSurface)
      (primeLift S sC hdim hTree htrans eC E hE L e h2 f hdisj ε D) =
        liftedCurve S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj ε D :=
  RationalComponentPrimeCurves.closedImage_liftThrough S f eC CoverSurface (treeCopy ε) D

/-- Opposite coherent sheets give disjoint component-map images, for every original component pair. -/
theorem primeLift_disjoint_opposite (ε : Bool) (D F : ↥(irreducibleComponents C)) :
    Disjoint (Set.range (primeLift S sC hdim hTree htrans eC E hE L e h2 f hdisj ε D).base)
      (Set.range (primeLift S sC hdim hTree htrans eC E hE L e h2 f hdisj (!ε) F).base) := by
  have hwhole : Disjoint (Set.range (treeCopy ε).base) (Set.range (treeCopy (!ε)).base) := by
    cases ε
    · exact UnbranchedRationalTreeAmbientCopies.copy_disjoint
        sC hdim hTree htrans eC E hE L e f hdisj h2.ne_zero
    · exact (UnbranchedRationalTreeAmbientCopies.copy_disjoint
        sC hdim hTree htrans eC E hE L e f hdisj h2.ne_zero).symm
  exact hwhole.mono
    (RationalComponentPrimeCurves.range_liftThrough_subset S f eC (treeCopy ε) D)
    (RationalComponentPrimeCurves.range_liftThrough_subset S f eC (treeCopy (!ε)) F)

/-- The actual prime-curve family retains all original components under both distinct labels. -/
theorem liftedCurve_injective : Function.Injective
    (fun i : Bool × ↥(irreducibleComponents C) =>
      liftedCurve S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj i.1 i.2) := by
  intro i j hij
  apply UnbranchedRationalTreeAmbientComponentCopies.componentImage_injective
    sC hdim hTree htrans eC E hE L e f hdisj h2.ne_zero
  exact congrArg (fun P : (CoverSurface).PrimeCurve => (P : Set (CoverSurface).toScheme)) hij

/-- The actual prime-curve family has precisely twice the original component count. -/
theorem liftedCurve_card :
    Nat.card (Set.range (fun i : Bool × ↥(irreducibleComponents C) =>
      liftedCurve S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj i.1 i.2)) =
        2 * Nat.card ↥(irreducibleComponents C) := by
  rw [Nat.card_range_of_injective (liftedCurve_injective
    S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj), Nat.card_prod]
  have hBool : Nat.card Bool = 2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [hBool]

end KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.liftedCurve_card
#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.primeLift_projection
#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.primeLift_disjoint_opposite
