import KltDP.Geometry.UnbranchedRationalQuadraticCoordinates
import KltDP.Geometry.QuadraticAtlasGlobalSplitting

/-!
# The actual pulled-line cover splits on a branch-disjoint rational curve

This joins the actual geometric half-line/root construction with the
original quadratic scheme gluing. The output is an actual isomorphism
over the original rational curve, without local roots or gluing equations
as premises. Comparison with the pullback of the ambient cover is separate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u

namespace KltDP.Geometry.UnbranchedRationalLineCoverSplit

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open QuadraticGlobalRootCoordinates UnbranchedRationalQuadraticCoordinates
open InvertibleQuadraticAtlas TransitionUnitGluing

/-- The literal pulled half-line atlas is isomorphic to two original copies
of the rational curve, and the isomorphism preserves its original projection. -/
theorem exists_split_over_base (k : Type u) [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X] [C.IsSeparated]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (f : C ⟶ X) (eC : C ≅ projectiveSpace k 1)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base))
    (h2 : IsUnit (2 : Γ(C, ⊤))) :
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
  obtain ⟨t, b, hs⟩ := exists_roots k E hE L e f eC hdisj
  let a : ∀ i, Γ(C, D.opens i)ˣ := rootUnit C (pullbackInvertibleSheaf f L) t b
  have hr : ∀ i j, res C (inf_le_left : D.opens i ⊓ D.opens j ≤ D.opens i)
      (a i : Γ(C, D.opens i)) = (D.units i j : Γ(C, D.opens i ⊓ D.opens j)) *
        res C inf_le_right (a j : Γ(C, D.opens j)) :=
    rootUnit_overlap C (pullbackInvertibleSheaf f L) t b
  have h2i (i) : IsUnit (2 : Γ(C, D.opens i)) := by
    simpa only [map_ofNat] using h2.map (res C (show D.opens i ≤ ⊤ from le_top))
  exact ⟨QuadraticAtlasGlobalSplitting.splitIso D a hs hr h2i,
    QuadraticAtlasGlobalSplitting.splitIso_hom_fold D a hs hr h2i⟩

end KltDP.Geometry.UnbranchedRationalLineCoverSplit

#print axioms KltDP.Geometry.UnbranchedRationalLineCoverSplit.exists_split_over_base
