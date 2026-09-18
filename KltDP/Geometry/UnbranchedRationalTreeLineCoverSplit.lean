import KltDP.Geometry.UnbranchedRationalTreeQuadraticCoordinates
import KltDP.Geometry.QuadraticAtlasGlobalSplitting

/-!
# The original pulled-line double cover splits over a whole rational tree

The actual Picard and branch-section arguments derive the roots and their
compatibility on every component and node. In odd characteristic the original
scheme gluing therefore splits over the original tree. Identifying this
pulled-line cover with the pullback of the ambient cover is separate.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedRationalTreeLineCoverSplit

local instance moduleTensor (C : Scheme.{u}) : MonoidalCategory C.Modules :=
  Scheme.Modules.monoidalCategory C

open RationalTreePicard QuadraticGlobalRootCoordinates UnbranchedRationalQuadraticCoordinates
open InvertibleQuadraticAtlas TransitionUnitGluing

/-- The original atlas of the pulled half-line is two copies of the entire
tree, with its original projection, without supplied roots or overlap equations. -/
theorem exists_split_over_base
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
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base))
    (h2 : (2 : k) ≠ 0) :
    let D := fromSquareRoot C (pullbackInvertibleSheaf f L)
      ((schemeModulePullback f).obj (cartierDivisorModule X E))
      (pulledSquareIso f L (cartierDivisorModule X E) e)
      (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
        (effectiveCartierSection X E hE))
    ∃ q : D.scheme ≅ C ⨿ C, q.hom ≫ coprod.desc (𝟙 C) (𝟙 C) = D.morphism := by
  let D := fromSquareRoot C (pullbackInvertibleSheaf f L)
    ((schemeModulePullback f).obj (cartierDivisorModule X E))
    (pulledSquareIso f L (cartierDivisorModule X E) e)
    (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
      (effectiveCartierSection X E hE))
  obtain ⟨t, b, hs⟩ := UnbranchedRationalTreeQuadraticCoordinates.exists_roots
    sC hdim hTree htrans eC E hE L e f hdisj
  let a : ∀ i, Γ(C, D.opens i)ˣ := rootUnit C (pullbackInvertibleSheaf f L) t b
  have hr : ∀ i j, res C (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
      (a i : Γ(C, D.opens i)) = (D.units i j : Γ(C, D.opens i ⊓ D.opens j)) *
        res C inf_le_right (a j : Γ(C, D.opens j)) :=
    rootUnit_overlap C (pullbackInvertibleSheaf f L) t b
  have h2global : IsUnit (2 : Γ(C, ⊤)) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr h2).map (baseFieldToGlobalSections sC)
  have h2i (i) : IsUnit (2 : Γ(C, D.opens i)) := by
    simpa only [map_ofNat] using h2global.map (res C (show D.opens i ≤ ⊤ from le_top))
  exact ⟨QuadraticAtlasGlobalSplitting.splitIso D a hs hr h2i,
    QuadraticAtlasGlobalSplitting.splitIso_hom_fold D a hs hr h2i⟩

end KltDP.Geometry.UnbranchedRationalTreeLineCoverSplit

#print axioms KltDP.Geometry.UnbranchedRationalTreeLineCoverSplit.exists_split_over_base
