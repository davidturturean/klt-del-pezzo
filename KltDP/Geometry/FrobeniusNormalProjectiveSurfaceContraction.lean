import KltDP.Geometry.FrobeniusGeneratedNormalImageCount
import KltDP.Geometry.GeneratedCompleteSystemNormalSurface
import KltDP.Geometry.GeneratedCompleteSystemNormalAmple
import KltDP.Geometry.FrobeniusMultiCentreNormalNullPrimes
import KltDP.Geometry.SemiampleLargePower

/-!
Choose a positive generated birational power of the original Frobenius
line and retain its actual generated normal factor. Its already constructed
target is bundled as a normal projective surface. The same source map
retains the ample-power pullback, exact prime labels, and the proved
number of distinct images of the independently defined null locus.
No singularity or minimal-resolution assertion is included.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreExceptionalPrime GeneratedCompleteSystemNormalFactor

attribute [local instance] KeelCompleteSystem.completeSystemDomain_isIntegral
  KeelCompleteSystem.completeSystemImage_isIntegral

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- The same original Frobenius contraction has an actual normal projective
surface target and exactly `2*n+1` distinct images of its actual null locus. -/
theorem exists_normal_projective_surface_contraction (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (S : NormalProjectiveSurface k)
      (π : multiSurface (q + 1) n a ⟶ S.toScheme),
      π ≫ S.structureMorphism = multiStructure (q + 1) n a ∧
      IsProper π ∧ Surjective π ∧ IsBirationalScheme π ∧ IsIso π.c ∧
      (∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ S.toScheme),
        ConnectedSpace (pullback π y : Scheme.{u})) ∧
      (∀ y : S.toScheme, IsConnected (π.base ⁻¹' {y})) ∧
      ∃ A : InvertibleSheaf S.toScheme, AmpleSerre.IsAmple A ∧
        Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj) ∧
        (∀ C : (multiSurfaceSurface (q + 1) n a ha
            (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
          (∃ p : Spec (CommRingCat.of k) ⟶ S.toScheme,
            C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ S.structureMorphism = 𝟙 _) ↔
          C = graphPrimeCurve q n a ha (originalMultiStructureProjective k (q + 1) n a) ∨
          (∃ i : Fin n, C = fiberPrimeCurve q n a ha
            (originalMultiStructureProjective k (q + 1) n a) i) ∨
          ∃ (i : Fin n) (j : Fin q), C = exceptionalPrimeCurveSPn q n a ha i (.inl j)
            (originalMultiStructureProjective k (q + 1) n a)) ∧
        (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
          (originalLine q n a ha)).Finite ∧
        Nat.card (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
          (originalLine q n a ha)) = 2 * n + 1 := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  letI : IsProper (multiStructure (q + 1) n a) :=
    (originalMultiStructureProjective k (q + 1) n a).isProper
  let X : NormalProjectiveSurface k := multiSurfaceSurface (q + 1) n a ha
    (originalMultiStructureProjective k (q + 1) n a)
  obtain ⟨N, _, hN⟩ := originalLine_eventuallyBirational q n a ha hn
  obtain ⟨m, hm, hmN, hG⟩ := SemiampleActualPowers.exists_globallyGenerated_power_ge
    (originalLine q n a ha) (originalLine_isSemiample q n a ha hn) N
  obtain ⟨hpos, hbir⟩ := hN m hmN
  let S : NormalProjectiveSurface k :=
    normalProjectiveSurface X (power (originalLine q n a ha) m) hpos hG hbir
  let π : multiSurface (q + 1) n a ⟶ S.toScheme :=
    fromSource (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG
  letI : IsProper S.structureMorphism := S.projective.isProper
  letI : IsLocallyNoetherian S.toScheme :=
    isLocallyNoetherian_of_locallyOfFiniteType_spec S.structureMorphism
  letI : IsProper π := fromSource_isProper
    (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG
  letI : IsIso π.c := fromSource_c_isIso
    (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG
  refine ⟨m, hm, S, π,
    fromSource_structure (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG,
    fromSource_isProper (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG,
    fromSource_surjective (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG,
    fromSource_isBirationalScheme (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG hbir,
    fromSource_c_isIso (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG,
    ProperSteinConnected.geometrically_connected π,
    ProperSteinConnected.pointFibers_connected π,
    line (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG,
    line_isAmple (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG,
    ⟨fromSource_pullbackLineIso (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG⟩, ?_, ?_⟩
  · intro C
    exact (PrimeCurveImageContraction.generatedNormal_factors_iff X C
      (originalLine q n a ha) m hm hpos hG).trans
        (originalLine_degree_zero_iff_labels q n a ha hn C)
  · exact FrobeniusNormalFactorImageCount.generated_image_nullLocus_finite_card
      q n a ha hn m hm hpos hG hbir

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
