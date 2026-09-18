import KltDP.Geometry.GenusZeroCartierPointSections
import KltDP.Geometry.GenusZeroCartierPointGeneration
import KltDP.Geometry.CompleteLinearSystemGlobalGeneration

/-! The original degree-one Cartier point linear system gives a whole-source P1 map.
Its dimension and global generation are proved from original H1(O)=0. The
actual projective degree-one sheaf pulls back to the original O(E).
This is a point-dependent producer, not the final genus-zero-to-P1 isomorphism. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CartierRationalPoint

open ModuleCohomology CompleteLinearSystemSections InvertibleSectionNonvanishingOpen

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
  (i : Spec (CommRingCat.of k) ⟶ X) [hiClosed : IsClosedImmersion i]
  (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X E hE)

include hiClosed hker in
/-- The original proper integral source maps to P1 by its actual complete point system.
No section dimension, global generation, projective map, or pullback isomorphism is assumed. -/
theorem exists_projectiveLine_morphism
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hi : i ≫ f = 𝟙 _)
    (hH1 : Subsingleton (H (_root_.SheafOfModules.unit X.ringCatSheaf) 1)) :
    ∃ g : X ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = f ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅ cartierDivisorModule X E) := by
  let L := cartierDivisorInvertibleSheaf X E
  have hdim : dimension f L = 2 := cohomologyDimension_eq_two E hE i hker f hi hH1
  have hpos : 0 < dimension f L := by omega
  have hL : Positivity.IsGloballyGenerated L.obj := isGloballyGenerated E hE i hker hH1
  have hcover : (⨆ j, nonvanishingOpen X L (positiveBasisSections f L hpos j)) = ⊤ :=
    CompleteLinearSystemGlobalGeneration.nonBaseOpen_eq_top f L hpos hL
  have hmap : ∃ g : X ⟶ projectiveSpace k (dimension f L - 1),
      g ≫ projectiveSpaceToSpec k (dimension f L - 1) = f ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k (dimension f L - 1))).obj ≅ L.obj) :=
    ⟨LinearSystemMorphism.morphism L (positiveBasisSections f L hpos) f hcover,
      LinearSystemMorphism.morphism_structure L (positiveBasisSections f L hpos) f hcover,
      ⟨LinearSystemPullback.pullbackDegreeOneIso L (positiveBasisSections f L hpos) f hcover⟩⟩
  have hindex : dimension f L - 1 = 1 := by omega
  exact Eq.mp (congrArg (fun n : ℕ =>
    ∃ g : X ⟶ projectiveSpace k n,
      g ≫ projectiveSpaceToSpec k n = f ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k n)).obj ≅ L.obj)) hindex) hmap

#print axioms exists_projectiveLine_morphism

end KltDP.Geometry.CartierRationalPoint
