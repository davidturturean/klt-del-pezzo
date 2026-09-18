import KltDP.Geometry.SplitPrimeCurveIntersection
import KltDP.Geometry.SplitAmbientPullbackLiftPairClassification

/-!
# Intersections of unchanged coherent lift maps

The maps themselves retain their original projections. Classification
identifies the chosen first-curve lift and both disjoint second-curve
lifts with their actual split copies, including the opposite label.
Cross-sheet disjointness then supplies the proved intersection formula.
No map-identification or label-comparison premise is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.SplitPrimeCurveLiftIntersection

open NormalProjectiveSurface SplitAmbientPullbackLiftClassification SplitPrimeCurveIntersection

variable {k : Type u} [Field k] [IsAlgClosed k] {S T : NormalProjectiveSurface k}
    (π : T.toScheme ⟶ S.toScheme) [GenericPointPreserving π] [QuasiCompact π]
    (C D : S.PrimeCurve)
    (qC : pullback π C.inclusion ≅ C.toScheme ⨿ C.toScheme)
    (qD : pullback π D.inclusion ≅ D.toScheme ⨿ D.toScheme)
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ x : T.Point, RegularPoint T.toScheme x)
    (hqC : qC.hom ≫ coprod.desc (𝟙 C.toScheme) (𝟙 C.toScheme) = pullback.snd π C.inclusion)
    (hqD : qD.hom ≫ coprod.desc (𝟙 D.toScheme) (𝟙 D.toScheme) = pullback.snd π D.inclusion)
    (hπ : π ≫ S.structureMorphism = T.structureMorphism)

include hqC hqD hπ in
/-- Actual coherent lifts preserve intersections, with closedness and label comparisons derived. -/
theorem lift_intersectionNumber
    (g : C.toScheme ⟶ T.toScheme) (d₀ d₁ : D.toScheme ⟶ T.toScheme)
    (hg : g ≫ π = C.inclusion) (hd₀ : d₀ ≫ π = D.inclusion) (hd₁ : d₁ ≫ π = D.inclusion)
    (hpair : Disjoint (Set.range d₀.base) (Set.range d₁.base))
    (hcross : Disjoint (Set.range g.base) (Set.range d₁.base)) :
    ∃ (hclosedG : IsClosedImmersion g) (hclosedD : IsClosedImmersion d₀),
      letI := hclosedG
      letI := hclosedD
      (C.closedImage (T := T) g).intersectionNumber
        (T.primeCurveCartier hT (D.closedImage (T := T) d₀)) =
          C.intersectionNumber (S.primeCurveCartier hS D) := by
  obtain ⟨ε, rfl⟩ := eq_ambientCopy_of_projection π C.inclusion qC hqC g hg
  obtain ⟨δ, rfl, rfl⟩ := eq_complementary_ambientCopies_of_projection
    π D.inclusion qD hqD d₀ d₁ hd₀ hd₁ hpair
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact copyCurve_intersectionNumber π C D qC qD hS hT hqC hπ ε δ hcross

end KltDP.Geometry.SplitPrimeCurveLiftIntersection

#print axioms KltDP.Geometry.SplitPrimeCurveLiftIntersection.lift_intersectionNumber
