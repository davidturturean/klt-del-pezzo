import KltDP.Geometry.UnbranchedRationalTreeBranchRoot
import KltDP.Geometry.UnbranchedRationalQuadraticCoordinates

/-!
# Coherent original quadratic roots on every component of a rational tree

One global frame and branch root on the whole tree determine roots of every
literal affine coefficient of the pulled-line quadratic atlas. The existing
root-coordinate overlap law consequently applies across all the tree nodes,
as well as within each component.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedRationalTreeQuadraticCoordinates

open RationalTreePicard InvertibleQuadraticAtlas QuadraticGlobalRootCoordinates
open UnbranchedRationalQuadraticCoordinates

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (C : Scheme.{u}) : MonoidalCategory C.Modules :=
  Scheme.Modules.monoidalCategory C

/-- Branch disjointness on the actual whole rational tree supplies the
original pulled-line atlas roots without componentwise compatibility assumptions. -/
theorem exists_roots
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X]
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
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base)) :
    ∃ (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf)
      (b : Γ(C, ⊤)ˣ), ∀ i,
      (rootUnit C (pullbackInvertibleSheaf f L) t b i :
        Γ(C, AffineOpenRefinement.opens C (pullbackInvertibleSheaf f L).localTrivializations.X i)) ^ 2 =
        (fromSquareRoot C (pullbackInvertibleSheaf f L)
          ((schemeModulePullback f).obj (cartierDivisorModule X E))
          (pulledSquareIso f L (cartierDivisorModule X E) e)
          (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
            (effectiveCartierSection X E hE))).sections i := by
  obtain ⟨t, b, hb⟩ := UnbranchedRationalTreeBranchRoot.exists_frame_and_root
    sC hdim hTree htrans eC E hE L e f hdisj
  have heq := pulled_square_section_eq f L (cartierDivisorModule X E) e
    (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
      (effectiveCartierSection X E hE)) t b hb
  refine ⟨t, b, ?_⟩
  intro i
  change _ = (fromSquareSection C (pullbackInvertibleSheaf f L) _).sections i
  rw [heq]
  exact rootUnit_sq C (pullbackInvertibleSheaf f L) t b i

end KltDP.Geometry.UnbranchedRationalTreeQuadraticCoordinates

#print axioms KltDP.Geometry.UnbranchedRationalTreeQuadraticCoordinates.exists_roots
