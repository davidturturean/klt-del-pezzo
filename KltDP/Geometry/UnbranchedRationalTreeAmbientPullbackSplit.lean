import KltDP.Geometry.UnbranchedRationalTreeBranchRoot
import KltDP.Geometry.UnbranchedAmbientPullbackSplit

/-!
# Two copies of the entire rational tree in the original ambient cover

The actual branch-disjoint tree supplies the global half-line frame and root.
The original ambient cover's base-change atlas and its proved comparison
with the scheme-theoretic pullback give the splitting, preserving the actual
second projection. No root, overlap compatibility, or splitting is supplied.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedRationalTreeAmbientPullbackSplit

local instance moduleTensor (C : Scheme.{u}) : MonoidalCategory C.Modules :=
  Scheme.Modules.monoidalCategory C

open RationalTreePicard InvertibleQuadraticAtlas

/-- The scheme-theoretic pullback of the original ambient double cover is
two copies of the whole original unbranched rational tree, over that tree. -/
theorem exists_split_over_base
    {k : Type u} [Field k] [IsAlgClosed k]
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
    (h2 : (2 : k) ≠ 0) :
    let D := fromSquareRoot X L (cartierDivisorModule X E) e
      (effectiveCartierSection X E hE)
    ∃ q : pullback D.morphism f ≅ C ⨿ C,
      q.hom ≫ coprod.desc (𝟙 C) (𝟙 C) = pullback.snd D.morphism f := by
  obtain ⟨t, b, hb⟩ := UnbranchedRationalTreeBranchRoot.exists_frame_and_root
    sC hdim hTree htrans eC E hE L e f hdisj
  have h2global : IsUnit (2 : Γ(C, ⊤)) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr h2).map (baseFieldToGlobalSections sC)
  exact UnbranchedAmbientPullbackSplit.exists_split_of_frame f L
    (cartierDivisorModule X E) e (effectiveCartierSection X E hE) t b hb h2global

end KltDP.Geometry.UnbranchedRationalTreeAmbientPullbackSplit

#print axioms KltDP.Geometry.UnbranchedRationalTreeAmbientPullbackSplit.exists_split_over_base
