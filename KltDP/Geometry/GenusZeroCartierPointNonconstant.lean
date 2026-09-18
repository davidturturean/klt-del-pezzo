import KltDP.Geometry.GenusZeroCartierPointMorphism
import KltDP.Geometry.CartierRationalPointDegree
import KltDP.Geometry.ProjectiveProper

/-! The original Cartier-point map is proper and cannot factor through the
original base point. A factorization would trivialize its pulled-back O(1),
contradicting the proved degree one of the original Cartier line.
The actual degree-one point remains an input; no isomorphism is asserted. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CartierRationalPoint

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (E : CartierDivisor X) (hE : HasRegularCartierEquations X E)
  (i : Spec (CommRingCat.of k) ⟶ X) [hiClosed : IsClosedImmersion i]
  (hker : i.ker = effectiveCartierIdealDataOfRegularEquations X E hE)

include hiClosed hker in
/-- A whole-source proper point-system map with actual degree-one pullback
cannot be a constant morphism through Spec k. No regularity of X is required. -/
theorem exists_proper_nonconstant_projectiveLine_morphism
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hi : i ≫ f = 𝟙 _) (hgenus : CurveCanonical.genus f = 0) :
    ∃ g : X ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = f ∧ IsProper g ∧
      Nonempty ((pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅ cartierDivisorModule X E) ∧
      ¬ ∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k 1, f ≫ p = g := by
  obtain ⟨g, hg, ⟨e⟩⟩ :=
    exists_projectiveLine_morphism_of_genus_zero E hE i hker f hi hgenus
  have hproper : IsProper g := by
    letI : IsProper (g ≫ projectiveSpaceToSpec k 1) := by
      rw [hg]
      infer_instance
    exact IsProper.of_comp_of_isSeparated g (projectiveSpaceToSpec k 1)
  refine ⟨g, hg, hproper, ⟨e⟩, ?_⟩
  rintro ⟨p, rfl⟩
  let L := ProjectiveSpaceDegreeOneSheaf.degreeOne k 1
  obtain ⟨ePoint⟩ := InvertibleSheafOnField.exists_unitIso k (pullbackInvertibleSheaf p L)
  let eUnit : cartierDivisorModule X E ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    e.symm ≪≫ ((schemeModulePullbackCompIso f p).app L.obj).symm ≪≫
      (schemeModulePullback f).mapIso ePoint ≪≫ schemeModulePullbackUnitIso f
  have hzero := eulerCharacteristic_eq_of_iso f eUnit
  have hone := eulerDegree_eq_one E hE i hker f hdim hi
  rw [hzero, sub_self] at hone
  exact zero_ne_one hone

#print axioms exists_proper_nonconstant_projectiveLine_morphism

end KltDP.Geometry.CartierRationalPoint
