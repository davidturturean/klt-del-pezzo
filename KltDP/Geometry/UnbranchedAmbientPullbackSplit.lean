import KltDP.Geometry.QuadraticAmbientBaseChangeSplit
import KltDP.Geometry.QuadraticCoverBaseChangeIso

/-!
# Splitting the scheme-theoretic pullback of the original ambient cover

The original coefficient and overlap equations split the actual base-change
atlas. Its proved geometric comparison identifies that atlas with the
scheme-theoretic pullback of the original ambient glued quadratic cover.
The resulting splitting preserves the original second pullback projection.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.UnbranchedAmbientPullbackSplit

attribute [local instance] Types.instFunLike Types.instConcreteCategory
local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleQuadraticAtlas RationalTreePicard

/-- The original branch-frame root splits the original actual scheme pullback. -/
theorem exists_split_of_frame {X Y : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated]
    (f : Y ⟶ X) (L : InvertibleSheaf X) (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (s : N.val.obj (op (⊤ : X.Opens)))
    (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (b : Γ(Y, ⊤)ˣ)
    (hb : (b : Γ(Y, ⊤)) ^ 2 =
      (UnbranchedRationalBranchRoot.squareFrame f L N e t).hom.val.app (op ⊤)
        (pulledSection f N ⊤ s)) (h2 : IsUnit (2 : Γ(Y, ⊤))) :
    let D := fromSquareRoot X L N e s
    ∃ q : pullback D.morphism f ≅ Y ⨿ Y,
      q.hom ≫ coprod.desc (𝟙 Y) (𝟙 Y) = pullback.snd D.morphism f := by
  let D := fromSquareRoot X L N e s
  obtain ⟨q, hq⟩ := QuadraticAmbientBaseChangeSplit.exists_split_of_frame
    f L N e s t b hb h2
  refine ⟨(D.baseChangeIso f).symm ≪≫ q, ?_⟩
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hq] using
    D.baseChangeIso_inv_morphism f

/-- An actual branch-disjoint rational curve has two copies in the original ambient cover. -/
theorem exists_split_on_rational_curve (k : Type u) [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X] [X.IsSeparated] [C.IsSeparated]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (f : C ⟶ X) (eC : C ≅ projectiveSpace k 1)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base))
    (h2 : IsUnit (2 : Γ(C, ⊤))) :
    let D := fromSquareRoot X L (cartierDivisorModule X E) e (effectiveCartierSection X E hE)
    ∃ q : pullback D.morphism f ≅ C ⨿ C,
      q.hom ≫ coprod.desc (𝟙 C) (𝟙 C) = pullback.snd D.morphism f := by
  obtain ⟨t, b, hb⟩ := UnbranchedRationalBranchRoot.exists_frame_and_root
    k E hE L e f eC hdisj
  exact exists_split_of_frame f L (cartierDivisorModule X E) e
    (effectiveCartierSection X E hE) t b hb h2

end KltDP.Geometry.UnbranchedAmbientPullbackSplit

#print axioms KltDP.Geometry.UnbranchedAmbientPullbackSplit.exists_split_on_rational_curve
