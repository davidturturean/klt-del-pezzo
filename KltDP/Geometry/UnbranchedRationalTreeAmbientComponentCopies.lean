import KltDP.Geometry.UnbranchedRationalTreeAmbientCopies
import KltDP.Geometry.SplitAmbientPullbackComponentCopies

/-!
# Both copies of every actual component of an unbranched rational tree

The original tree and branch data produce the splitting used here. Every
original reduced component has two actual closed immersions in the
original cover. Their image family has exactly twice the original
component cardinality. The conclusion does not assume a splitting,
distinct images, or a component count.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedRationalTreeAmbientComponentCopies

local instance moduleTensor (C : Scheme.{u}) : MonoidalCategory C.Modules :=
  Scheme.Modules.monoidalCategory C

open RationalTreePicard InvertibleQuadraticAtlas UnbranchedRationalTreeAmbientCopies

variable {k : Type u} [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    [NoetherianSpace C] [IsLocallyNoetherian C] [IsReduced C]
    [ConnectedSpace C] [C.IsSeparated]
    (sC : C ⟶ Spec (CommRingCat.of k)) [IsProper sC]
    (hdim : topologicalKrullDim C ≤ 1)
    (hTree : (componentPointIncidenceGraph C).IsTree)
    (htrans : HasTransverseComponentBranches C)
    (eC : ∀ D : ↥(irreducibleComponents C),
      componentUnionScheme C {D} ≅ projectiveSpace k 1)
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (f : C ⟶ X)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base))
    (h2 : (2 : k) ≠ 0)

/-- Each original reduced component maps through its actual labeled tree copy. -/
def componentCopy (ε : Bool) (D : ↥(irreducibleComponents C)) :
    componentUnionScheme C {D} ⟶
      (fromSquareRoot X L (cartierDivisorModule X E) e
        (effectiveCartierSection X E hE)).scheme :=
  componentUnionInclusion C {D} ≫ copy sC hdim hTree htrans eC E hE L e f hdisj h2 ε

instance componentCopy_isClosedImmersion [IsClosedImmersion f]
    (ε : Bool) (D : ↥(irreducibleComponents C)) :
    IsClosedImmersion (componentCopy sC hdim hTree htrans eC E hE L e f hdisj h2 ε D) := by
  dsimp only [componentCopy]
  infer_instance

/-- The map projects to precisely the original component inclusion in the original surface. -/
@[reassoc]
theorem componentCopy_projection (ε : Bool) (D : ↥(irreducibleComponents C)) :
    componentCopy sC hdim hTree htrans eC E hE L e f hdisj h2 ε D ≫
      (fromSquareRoot X L (cartierDivisorModule X E) e
        (effectiveCartierSection X E hE)).morphism = componentUnionInclusion C {D} ≫ f := by
  rw [componentCopy, Category.assoc, copy_projection]

/-- The actual ambient image family of both copies of every original component. -/
def componentImage (i : Bool × ↥(irreducibleComponents C)) :
    Set (fromSquareRoot X L (cartierDivisorModule X E) e
      (effectiveCartierSection X E hE)).scheme :=
  Set.range (componentCopy sC hdim hTree htrans eC E hE L e f hdisj h2 i.1 i.2).base

/-- All original components survive separately under both labels. -/
theorem componentImage_injective [IsClosedImmersion f] :
    Function.Injective (componentImage sC hdim hTree htrans eC E hE L e f hdisj h2) :=
  SplitAmbientPullbackComponentCopies.componentImage_injective _ f
    (splitting sC hdim hTree htrans eC E hE L e f hdisj h2)

/-- The actual image family has exactly twice as many members as the original components. -/
theorem componentImage_card [IsClosedImmersion f] :
    Nat.card (Set.range (componentImage sC hdim hTree htrans eC E hE L e f hdisj h2)) =
      2 * Nat.card ↥(irreducibleComponents C) :=
  SplitAmbientPullbackComponentCopies.componentImage_card _ f
    (splitting sC hdim hTree htrans eC E hE L e f hdisj h2)

end KltDP.Geometry.UnbranchedRationalTreeAmbientComponentCopies

#print axioms KltDP.Geometry.UnbranchedRationalTreeAmbientComponentCopies.componentImage_card
#print axioms KltDP.Geometry.UnbranchedRationalTreeAmbientComponentCopies.componentCopy_projection
