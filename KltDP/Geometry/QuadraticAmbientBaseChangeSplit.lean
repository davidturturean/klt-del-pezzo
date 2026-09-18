import KltDP.Geometry.QuadraticAmbientBaseChangeRoots
import KltDP.Geometry.QuadraticAtlasGlobalSplitting

/-!
# Splitting the actual base-change atlas of the original ambient cover

The actual branch-frame root supplies literal coefficient and transition
equations in the base-change atlas of the original ambient cover. The
proved global gluing theorem therefore splits that actual atlas over the
original new base. The rational-curve endpoint derives its frame and root
from branch disjointness. The geometric identification of this atlas with
the original scheme-theoretic pullback is provided separately.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.QuadraticAmbientBaseChangeSplit

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleQuadraticAtlas TransitionUnitGluing RationalTreePicard

/-- Actual global splitting of the original base-change atlas, preserving its base map. -/
theorem exists_split_of_frame {X Y : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
    (f : Y ⟶ X) (L : InvertibleSheaf X) (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (s : N.val.obj (op (⊤ : X.Opens)))
    (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (b : Γ(Y, ⊤)ˣ)
    (hb : (b : Γ(Y, ⊤)) ^ 2 =
      (UnbranchedRationalBranchRoot.squareFrame f L N e t).hom.val.app (op ⊤)
        (pulledSection f N ⊤ s)) (h2 : IsUnit (2 : Γ(Y, ⊤))) :
    let D := (fromSquareRoot X L N e s).baseChangeAtlas f
    ∃ q : D.scheme ≅ Y ⨿ Y, q.hom ≫ coprod.desc (𝟙 Y) (𝟙 Y) = D.morphism := by
  let D := (fromSquareRoot X L N e s).baseChangeAtlas f
  obtain ⟨a, ha, hr⟩ := QuadraticAmbientBaseChangeRoots.baseChange_roots_of_frame
    f L N e s t b hb
  have h2i (i) : IsUnit (2 : Γ(Y, D.opens i)) := by
    simpa only [map_ofNat] using h2.map (res Y (show D.opens i ≤ ⊤ from le_top))
  exact ⟨QuadraticAtlasGlobalSplitting.splitIso D a ha hr h2i,
    QuadraticAtlasGlobalSplitting.splitIso_hom_fold D a ha hr h2i⟩

/-- Branch disjointness supplies the actual ambient base-change splitting on a rational curve. -/
theorem exists_split_on_rational_curve (k : Type u) [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X] [X.IsSeparated] [C.IsSeparated]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (f : C ⟶ X) (eC : C ≅ projectiveSpace k 1)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base))
    (h2 : IsUnit (2 : Γ(C, ⊤))) :
    let D := (fromSquareRoot X L (cartierDivisorModule X E) e
      (effectiveCartierSection X E hE)).baseChangeAtlas f
    ∃ q : D.scheme ≅ C ⨿ C, q.hom ≫ coprod.desc (𝟙 C) (𝟙 C) = D.morphism := by
  obtain ⟨t, b, hb⟩ := UnbranchedRationalBranchRoot.exists_frame_and_root
    k E hE L e f eC hdisj
  exact exists_split_of_frame f L (cartierDivisorModule X E) e
    (effectiveCartierSection X E hE) t b hb h2

end KltDP.Geometry.QuadraticAmbientBaseChangeSplit

#print axioms KltDP.Geometry.QuadraticAmbientBaseChangeSplit.exists_split_on_rational_curve
