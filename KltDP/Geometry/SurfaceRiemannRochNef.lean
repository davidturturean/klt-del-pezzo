import KltDP.Geometry.NefIntersectionSectionVanishing
import KltDP.Geometry.SurfaceRiemannRochProved

/-!
# Effective original divisors from RR and negative complementary intersection

The actual geometric nef-intersection criterion now supplies the
complementary-section vanishing required by the full surface RR consumer.
The remaining hypotheses concern the original canonical divisor, an actual
nef or ample Cartier class, and the displayed numerical inequalities.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SmoothCanonicalCartierRepresentative

universe u

namespace KltDP.Geometry.SurfaceRiemannRochNef

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The strict comparison of the original intersections of K and D is
exactly the negative complementary-intersection condition. -/
theorem complementary_intersection_neg (D K : X.WeilDivisor)
    (A : CartierDivisor X.toScheme)
    (hdegree : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm K) A <
        intersectionPairing X hregular ((X.regularCartierWeilEquiv hregular).symm D) A) :
    intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm (K - D)) A < 0 := by
  rw [map_sub, sub_eq_add_neg, X.intersectionPairing_add_left hregular,
    X.intersectionPairing_neg_left hregular, ← sub_eq_add_neg]
  exact sub_lt_zero.mpr hdegree

/-- Actual nefness and the intersection comparison discharge the
complementary-section premise of RR and give an original nonzero section. -/
theorem exists_nonzero_section (D K : X.WeilDivisor) (A : CartierDivisor X.toScheme)
    (hK : IsCanonical X hregular K)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hdegree : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm K) A <
        intersectionPairing X hregular ((X.regularCartierWeilEquiv hregular).symm D) A)
    (hpositive : 0 < rrNumber X hregular D K) :
    ∃ s : sections (divisorModule X hregular D), s ≠ 0 :=
  SurfaceRiemannRochProved.exists_nonzero_section X hregular D K hK
    (NefIntersectionSectionVanishing.sections_subsingleton X hregular (K - D) A hA
      (complementary_intersection_neg X hregular D K A hdegree)) hpositive

/-- The produced nonzero section yields an effective integral divisor in
the original linear-equivalence class; no section-vanishing input remains. -/
theorem exists_effectiveWeil (D K : X.WeilDivisor) (A : CartierDivisor X.toScheme)
    (hK : IsCanonical X hregular K)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hdegree : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm K) A <
        intersectionPairing X hregular ((X.regularCartierWeilEquiv hregular).symm D) A)
    (hpositive : 0 < rrNumber X hregular D K) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧ X.LinearlyEquivalent Z D := by
  obtain ⟨s, hs⟩ := exists_nonzero_section X hregular D K A hK hA hdegree hpositive
  exact X.exists_effectiveWeil_of_nonzero_section hregular D s hs

/-- The same actual effective-divisor conclusion with Serre ampleness of
the original Cartier line bundle as the geometric positivity hypothesis. -/
theorem exists_effectiveWeil_of_isAmple
    (D K : X.WeilDivisor) (A : CartierDivisor X.toScheme)
    (hK : IsCanonical X hregular K)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (hdegree : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm K) A <
        intersectionPairing X hregular ((X.regularCartierWeilEquiv hregular).symm D) A)
    (hpositive : 0 < rrNumber X hregular D K) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧ X.LinearlyEquivalent Z D :=
  exists_effectiveWeil X hregular D K A hK
    (AmpleNefUnconditional.isNef_of_isAmple X
      (cartierDivisorInvertibleSheaf X.toScheme A) hA) hdegree hpositive

section SmoothConsumer

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- On the original smooth surface, the constructed canonical divisor
supplies canonicality and the actual structure map supplies regularity. -/
theorem exists_effectiveWeil_of_constructedCanonical
    (D : X.WeilDivisor) (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hdegree : intersectionPairing X X.regularPoints_of_isSmooth
      ((X.regularCartierWeilEquiv X.regularPoints_of_isSmooth).symm (weilRepresentative X)) A <
        intersectionPairing X X.regularPoints_of_isSmooth
          ((X.regularCartierWeilEquiv X.regularPoints_of_isSmooth).symm D) A)
    (hpositive : 0 < rrNumber X X.regularPoints_of_isSmooth D (weilRepresentative X)) :
    ∃ Z : X.WeilDivisor, EffectiveDivisor Z ∧ X.LinearlyEquivalent Z D :=
  exists_effectiveWeil X X.regularPoints_of_isSmooth D (weilRepresentative X) A
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical X) hA hdegree hpositive

end SmoothConsumer

end KltDP.Geometry.SurfaceRiemannRochNef
