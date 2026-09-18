import KltDP.Examples.FrobeniusRulingFiberMeetsGraph
import KltDP.Examples.FrobeniusMultiCentreIntegral
import KltDP.Geometry.MinimalResolutionCount
import KltDP.Geometry.PrimeCurveCodimension
import KltDP.Geometry.PrimeCurveOfClosedImmersion

/-!
# A prime curve in a nonspecial finite ruling fiber meets the original graph

The accepted unaffected-fiber lift is a closed projective line. Its range is
the preimage of the original finite point under the original second ruling.
Prime-curve maximality derives equality with that range from containment;
the independently proved graph-meeting point then belongs to the curve.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusNonspecialRulingPrimeCurve

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGraphClosed
  FrobeniusGraphPicardClassZeroFiber FrobeniusMultiCentreSurface
  FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreGraphContacts
  FrobeniusMultiCentreIntegral FrobeniusSpecialFiberSPn
  FrobeniusNonspecialRulingMeetsGraph

variable {k : Type u} [Field k]

/-- An actual rational section has the singleton range given by its original point. -/
theorem range_fieldMorphism {X : Scheme.{u}} (s : Spec (CommRingCat.of k) ⟶ X) :
    Set.range s.base = {fieldMorphismPoint s} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subsingleton.elim y (IsLocalRing.closedPoint k)]
    rfl
  · intro hx
    exact ⟨IsLocalRing.closedPoint k, hx.symm⟩

/-- The range formula for the original maps of an actual scheme pullback square. -/
theorem range_eq_preimage_of_isPullback {W X Y Z : Scheme.{u}}
    {i : W ⟶ X} {j : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback i j f g) : Set.range i.base = f.base ⁻¹' Set.range g.base := by
  rw [← h.isoPullback_hom_fst, range_iso_comp_base, Scheme.Pullback.range_fst]

/-- Containment in an actual closed projective line forces equality for an original prime curve. -/
theorem primeCurve_eq_range (X : NormalProjectiveSurface k)
    {Y : Scheme.{u}} (i : Y ⟶ X.toScheme) [IsClosedImmersion i]
    (e : Y ≅ projectiveSpace k 1) (C : X.PrimeCurve)
    (hC : (C : Set X.toScheme) ⊆ Set.range i.base) :
    (C : Set X.toScheme) = Set.range i.base := by
  let F := PrimeCurveOfClosedImmersion.primeCurveOfIsoProjectiveLine X i e
  exact C.coe_eq_of_subset_irreducibleCloseds F.1 hC F.ne_univ

/-- The original horizontal finite fiber has precisely the expected point support. -/
theorem range_horizontalFiberMorphism (c : k) :
    Set.range (horizontalFiberMorphism c).base =
      (secondProjection (k := k)).base ⁻¹' {point c} := by
  rw [← horizontalFiberIso_hom_fst, range_iso_comp_base,
    Scheme.Pullback.range_fst, range_fieldMorphism] <;> rfl

variable [IsAlgClosed k]
variable (q n : ℕ) (a : Fin n → k)

/-- The accepted unaffected lift is the entire original finite ruling support. -/
theorem range_unaffectedFiberLift (c : k) (hc : ∀ j, c ≠ a j ^ (q + 1)) :
    Set.range (unaffectedFiberLift q n a c hc).base =
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {point c} := by
  rw [range_eq_preimage_of_isPullback (unaffectedFiberLift_isPullback q n a c hc),
    range_horizontalFiberMorphism] <;> rfl

variable [Fact (q + 1).Prime] [CharP k (q + 1)]
variable (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Every original prime curve contained in a nonspecial finite ruling fiber meets the strict graph. -/
theorem finite_primeCurve_meets_graphStrict
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve)
    (c : k) (hc : ∀ j, c ≠ a j ^ (q + 1))
    (hC : (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) ⊆
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {point c}) :
    ((C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) ∩
      Set.range (graphStrictι (q + 1) n a).base).Nonempty := by
  letI : IsClosedImmersion (unaffectedFiberLift q n a c hc) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (unaffectedFiberLift_isPullback q n a c hc).flip inferInstance
  have heq := primeCurve_eq_range (multiSurfaceSurface (q + 1) n a ha hproj)
    (unaffectedFiberLift q n a c hc) (Iso.refl _) C
    ((range_unaffectedFiberLift q n a c hc).symm ▸ hC)
  rw [heq]
  exact unaffectedFiberLift_meets_graphStrict q n a c hc

/-- An original prime curve in a nonspecial finite ruling fiber cannot be graph-disjoint. -/
theorem finite_primeCurve_not_disjoint_graphStrict
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve)
    (c : k) (hc : ∀ j, c ≠ a j ^ (q + 1))
    (hC : (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) ⊆
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {point c})
    (hdisj : Disjoint (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme)
      (Set.range (graphStrictι (q + 1) n a).base)) : False := by
  obtain ⟨z, hzC, hzB⟩ := finite_primeCurve_meets_graphStrict q n a ha hproj C c hc hC
  exact Set.disjoint_left.mp hdisj hzC hzB

end KltDP.Examples.FrobeniusNonspecialRulingPrimeCurve
