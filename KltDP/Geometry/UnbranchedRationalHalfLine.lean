import KltDP.Geometry.UnbranchedCartierPullbackUnit
import KltDP.Geometry.RationalCurveSquareTriviality

/-!
# The original half-line restricts trivially to a branch-disjoint rational curve

The square is the original Cartier line, and branch disjointness concerns
its actual zero scheme. Neither the restricted square trivialization nor
the half-line trivialization is supplied as a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.UnbranchedRationalHalfLine

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Restriction of the actual square follows from the branch-disjoint original map. -/
def squareUnitIso {X C : Scheme.{u}} [IsIntegral X]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (f : C ⟶ X) (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base)) :
    (pullbackInvertibleSheaf f L).obj ⊗ (pullbackInvertibleSheaf f L).obj ≅
      _root_.SheafOfModules.unit C.ringCatSheaf :=
  (schemeModulePullbackTensorIso f L.obj L.obj).symm ≪≫
    (schemeModulePullback f).mapIso e ≪≫ UnbranchedCartierPullback.unitIso E hE f hdisj

/-- The half-line itself is trivial on the original rational curve. -/
def unitIso (k : Type u) [Field k] {X C : Scheme.{u}} [IsIntegral X]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (f : C ⟶ X) (eC : C ≅ projectiveSpace k 1)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base)) :
    (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf :=
  RationalCurveSquareTriviality.unitIsoOfSquareIso k eC (pullbackInvertibleSheaf f L)
    (squareUnitIso E hE L e f hdisj)

end KltDP.Geometry.UnbranchedRationalHalfLine
