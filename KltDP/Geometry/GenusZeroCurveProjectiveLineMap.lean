import KltDP.Geometry.IntegralRegularClosedPoint
import KltDP.Geometry.RegularCurvePointCartier
import KltDP.Geometry.GenusZeroCartierPointNonconstant

/-! The original proper integral genus-zero curve has a proper nonconstant
map to the projective line whose actual degree-one sheaf has degree-one
pullback. A regular closed point, its Cartier divisor, the full section
dimension, global generation, and the original map are all constructed.
The later finite degree-one isomorphism argument is not assumed here. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.GenusZeroCurveProjectiveLineMap

open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [hproper : IsProper f]

include hproper in
/-- The actual source maps to P1 with a proved degree-one O(1) pullback.
No chosen point, Cartier divisor, section system, or morphism is an input. -/
theorem exists_proper_morphism_with_degree_one
    (hdim : topologicalKrullDim X = 1) (hgenus : CurveCanonical.genus f = 0) :
    ∃ g : X ⟶ projectiveSpace k 1,
      g ≫ projectiveSpaceToSpec k 1 = f ∧ IsProper g ∧
      (eulerCharacteristic f (pullbackInvertibleSheaf g
        (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj -
        eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1) ∧
      ¬ ∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k 1, f ≫ p = g := by
  have hdim₂ : topologicalKrullDim X ≤ 2 := by rw [hdim]; norm_num
  obtain ⟨x, hclosed, hregular⟩ :=
    IntegralRegularClosedPoint.exists_closed_regularPoint f hdim₂
  obtain ⟨E, hE, hker⟩ :=
    RegularCurvePointCartier.exists_cartierDivisor f x hclosed hregular hdim
  let i := closedPointSection f x hclosed
  letI : IsClosedImmersion (X.fromSpecResidueField x) :=
    fromSpecResidueField_isClosedImmersion X x hclosed
  letI : IsClosedImmersion i := by
    dsimp [i, closedPointSection]
    infer_instance
  have hi : i ≫ f = 𝟙 _ := closedPointSection_over_base f x hclosed
  obtain ⟨g, hg, hgp, ⟨e⟩, hng⟩ :=
    CartierRationalPoint.exists_proper_nonconstant_projectiveLine_morphism
      E hE i hker f hdim.le hi hgenus
  refine ⟨g, hg, hgp, ?_, hng⟩
  rw [eulerCharacteristic_eq_of_iso f e]
  exact CartierRationalPoint.eulerDegree_eq_one E hE i hker f hdim.le hi

#print axioms exists_proper_morphism_with_degree_one

end KltDP.Geometry.GenusZeroCurveProjectiveLineMap
