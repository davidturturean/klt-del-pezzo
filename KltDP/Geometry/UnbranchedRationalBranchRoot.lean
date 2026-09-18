import KltDP.Geometry.UnbranchedRationalHalfLine
import KltDP.Geometry.UnbranchedCanonicalSectionRoot
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.ProjectiveSpaceIntegral

/-!
# The actual half-line frame and the original branch square root

The rational-curve isomorphism and branch disjointness construct the half-line
frame. The original square isomorphism induces its frame on the pulled
Cartier line; the literal pulled canonical section has a unit square root in
that frame. Neither a frame nor a nonzero coefficient is a premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
universe u

namespace KltDP.Geometry.UnbranchedRationalBranchRoot

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The original square isomorphism carries the square of the actual half-line
frame to a frame of the original pulled branch line. -/
def squareFrame {X C : Scheme.{u}} (f : C ⟶ X) (L : InvertibleSheaf X)
    (N : X.Modules) (e : L.obj ⊗ L.obj ≅ N)
    (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf) :
    (schemeModulePullback f).obj N ≅ _root_.SheafOfModules.unit C.ringCatSheaf :=
  (schemeModulePullback f).mapIso e.symm ≪≫ schemeModulePullbackTensorIso f L.obj L.obj ≪≫
    tensorIso t t ≪≫
    tensorIso (SchemeModuleStructureUnit.iso C) (SchemeModuleStructureUnit.iso C) ≪≫
    λ_ (𝟙_ C.Modules) ≪≫ (SchemeModuleStructureUnit.iso C).symm

/-- The actual rational-curve construction supplies both the half-line frame
and the unit root of the original pulled canonical branch coefficient. -/
theorem exists_frame_and_root (k : Type u) [Field k] [IsAlgClosed k]
    {X C : Scheme.{u}} [IsIntegral X]
    (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
    (L : InvertibleSheaf X) (e : L.obj ⊗ L.obj ≅ cartierDivisorModule X E)
    (f : C ⟶ X) (eC : C ≅ projectiveSpace k 1)
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations X E hE).gluedTo.base)) :
    ∃ (t : (pullbackInvertibleSheaf f L).obj ≅ _root_.SheafOfModules.unit C.ringCatSheaf)
      (b : Γ(C, ⊤)ˣ),
      (b : Γ(C, ⊤)) ^ 2 =
        (squareFrame f L (cartierDivisorModule X E) e t).hom.val.app (op (f ⁻¹ᵁ ⊤))
          (RationalTreePicard.pulledSection f (cartierDivisorModule X E) ⊤
            (effectiveCartierSection X E hE)) := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : Nonempty C := ⟨eC.inv.base (Classical.choice inferInstance)⟩
  letI : IsIntegral C := isIntegral_of_isOpenImmersion eC.hom
  letI : LocallyOfFiniteType (projectiveSpaceToSpec k 1) :=
    projectiveSpaceToSpec_locallyOfFiniteType k 1
  let t := UnbranchedRationalHalfLine.unitIso k E hE L e f eC hdisj
  obtain ⟨b, hb⟩ := UnbranchedCanonicalSection.exists_unit_square_root
    (eC.hom ≫ projectiveSpaceToSpec k 1) E hE f hdisj
    (squareFrame f L (cartierDivisorModule X E) e t)
  exact ⟨t, b, hb⟩

end KltDP.Geometry.UnbranchedRationalBranchRoot

#print axioms KltDP.Geometry.UnbranchedRationalBranchRoot.exists_frame_and_root
