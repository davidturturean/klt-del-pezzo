import KltDP.Geometry.SplitAmbientPullbackCopies
import KltDP.Geometry.UnbranchedRationalTreeAmbientPullbackSplit

/-!
# Both actual labeled rational-tree copies in the original ambient cover

The original branch-disjoint rational tree supplies its actual pullback
splitting. The two maps below are constructed using its inverse and the
original first pullback projection. Their compatibility, disjointness and
closed-immersion properties are proved from the actual construction; none
of those geometric conclusions is a hypothesis.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedRationalTreeAmbientCopies

local instance moduleTensor (C : Scheme.{u}) : MonoidalCategory C.Modules :=
  Scheme.Modules.monoidalCategory C

open RationalTreePicard InvertibleQuadraticAtlas

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

/-- The actual original-ambient splitting, obtained from the original tree and branch data. -/
def splitting :
    pullback (fromSquareRoot X L (cartierDivisorModule X E) e
      (effectiveCartierSection X E hE)).morphism f ≅ C ⨿ C :=
  Classical.choose (UnbranchedRationalTreeAmbientPullbackSplit.exists_split_over_base
    sC hdim hTree htrans eC E hE L e f hdisj h2)

theorem splitting_over_base :
    (splitting sC hdim hTree htrans eC E hE L e f hdisj h2).hom ≫
      coprod.desc (𝟙 C) (𝟙 C) =
        pullback.snd (fromSquareRoot X L (cartierDivisorModule X E) e
          (effectiveCartierSection X E hE)).morphism f :=
  Classical.choose_spec (UnbranchedRationalTreeAmbientPullbackSplit.exists_split_over_base
    sC hdim hTree htrans eC E hE L e f hdisj h2)

/-- The two labeled maps into the original ambient cover, using the original pullback projection. -/
def copy (ε : Bool) : C ⟶
    (fromSquareRoot X L (cartierDivisorModule X E) e (effectiveCartierSection X E hE)).scheme :=
  SplitAmbientPullbackCopies.ambientCopy _ f
    (splitting sC hdim hTree htrans eC E hE L e f hdisj h2) ε

/-- Both actual maps project to the original tree inclusion. -/
@[reassoc]
theorem copy_projection (ε : Bool) :
    copy sC hdim hTree htrans eC E hE L e f hdisj h2 ε ≫
      (fromSquareRoot X L (cartierDivisorModule X E) e (effectiveCartierSection X E hE)).morphism = f :=
  SplitAmbientPullbackCopies.ambientCopy_projection _ f
    (splitting sC hdim hTree htrans eC E hE L e f hdisj h2)
    (splitting_over_base sC hdim hTree htrans eC E hE L e f hdisj h2) ε

/-- For an actual closed tree inclusion, both derived ambient maps are closed immersions. -/
instance copy_isClosedImmersion [IsClosedImmersion f] (ε : Bool) :
    IsClosedImmersion (copy sC hdim hTree htrans eC E hE L e f hdisj h2 ε) :=
  SplitAmbientPullbackCopies.ambientCopy_isClosedImmersion _ f
    (splitting sC hdim hTree htrans eC E hE L e f hdisj h2) ε

/-- The original preimmersion gives two disjoint image ranges in the actual ambient cover. -/
theorem copy_disjoint [IsPreimmersion f] :
    Disjoint (Set.range (copy sC hdim hTree htrans eC E hE L e f hdisj h2 false).base)
      (Set.range (copy sC hdim hTree htrans eC E hE L e f hdisj h2 true).base) :=
  SplitAmbientPullbackCopies.ambientCopy_disjoint _ f
    (splitting sC hdim hTree htrans eC E hE L e f hdisj h2)

end KltDP.Geometry.UnbranchedRationalTreeAmbientCopies

#print axioms KltDP.Geometry.UnbranchedRationalTreeAmbientCopies.copy_projection
#print axioms KltDP.Geometry.UnbranchedRationalTreeAmbientCopies.copy_disjoint
