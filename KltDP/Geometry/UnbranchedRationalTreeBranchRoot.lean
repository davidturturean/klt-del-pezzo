import KltDP.Geometry.RationalTreeSquareTriviality
import KltDP.Geometry.ConnectedReducedBranchRoot
import KltDP.Geometry.UnbranchedRationalBranchRoot

/-!
# An original global half-line frame and branch root on a whole rational tree

The original branch-disjoint map and the proved rational-tree Picard theorem
construct one global half-line frame. The original pulled branch section in
its induced square frame then has a unit square root. Neither the frame nor
any compatibility or root is an extra premise, including at the tree nodes.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedRationalTreeBranchRoot

open RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (C : Scheme.{u}) : MonoidalCategory C.Modules :=
  Scheme.Modules.monoidalCategory C

/-- The actual branch-disjoint rational tree supplies one global frame and
one unit root of the original branch coefficient, simultaneously on all components. -/
theorem exists_frame_and_root
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X]
    [NoetherianSpace C] [IsLocallyNoetherian C] [IsReduced C] [ConnectedSpace C]
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
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base)) :
    ∃ (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf)
      (b : Γ(C, ⊤)ˣ),
      (b : Γ(C, ⊤)) ^ 2 =
        (UnbranchedRationalBranchRoot.squareFrame f L (cartierDivisorModule X E) e t).hom.val.app
          (op (f ⁻¹ᵁ ⊤))
            (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
              (effectiveCartierSection X E hE)) := by
  let t := RationalTreeSquareTriviality.unbranchedHalfLineIso
    C sC hdim hTree htrans eC E hE L e f hdisj
  obtain ⟨b, hb⟩ := UnbranchedCanonicalSection.exists_unit_square_root_of_connected_reduced
    sC E hE f hdisj (UnbranchedRationalBranchRoot.squareFrame f L
      (cartierDivisorModule X E) e t)
  exact ⟨t, b, hb⟩

end KltDP.Geometry.UnbranchedRationalTreeBranchRoot

#print axioms KltDP.Geometry.UnbranchedRationalTreeBranchRoot.exists_frame_and_root
