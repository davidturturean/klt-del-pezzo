import KltDP.Geometry.FrobeniusNormalFactorNullLocusSaturation

/-!
The target open is the complement of the actual closed image of the
original null locus. Saturation identifies its original inverse-image
open with the original null-locus complement. No new support or fiber
exhaustion assumption is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreContractingNullLocus

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- The independently defined original null locus is the original
zero-degree prime union, with original projectivity supplied internally. -/
theorem originalNullLocus_eq_curveUnion (hn : 2 < n) :
    Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha) =
      ⋃ C ∈ {C : (multiSurfaceSurface (q + 1) n a ha
          (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve |
        C.restrictionDegree (originalLine q n a ha) = 0},
        (C : Set (multiSurfaceSurface (q + 1) n a ha
          (originalMultiStructureProjective k (q + 1) n a)).toScheme) :=
  (nullLocus_eq_support q n a ha
    (originalMultiStructureProjective k (q + 1) n a) hn).trans
    (null_curve_union_eq_support q n a ha
      (originalMultiStructureProjective k (q + 1) n a) hn).symm

/-- The actual complement of the null-locus image under the given proper map. -/
def nullImageComplement {Y : Scheme.{u}}
    (π : multiSurface (q + 1) n a ⟶ Y) [IsProper π] : Y.Opens :=
  ⟨(π.base '' Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha))ᶜ,
    (π.isClosedMap _ (Positivity.isClosed_nullLocus
      (multiStructure (q + 1) n a) (originalLine q n a ha))).isOpen_compl⟩

@[simp] theorem coe_nullImageComplement {Y : Scheme.{u}}
    (π : multiSurface (q + 1) n a ⟶ Y) [IsProper π] :
    (nullImageComplement q n a ha π : Set Y) =
      (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha))ᶜ := rfl

/-- The original inverse-image open is exactly the original null-locus complement. -/
theorem preimage_nullImageComplement (hn : 2 < n) (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme) [IsProper π] [Surjective π] :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∀ (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
      (hbir : IsBirationalScheme π)
      (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
      (hcriterion : ∀ C : (multiSurfaceSurface (q + 1) n a ha
          (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
        (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
          C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0),
      π ⁻¹ᵁ nullImageComplement q n a ha π =
        (Positivity.nullLocusClosed (multiStructure (q + 1) n a) (originalLine q n a ha)).compl := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion
  have hsat := nullLocus_preimage_image_of_prime_criterion
    q n a ha hn Y.structureMorphism π inferInstance inferInstance hπ hbir hconnected hcriterion
  ext x
  change (π.base x ∉ π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha)) ↔
    x ∉ Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha)
  exact not_congr (Set.ext_iff.mp hsat x)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
