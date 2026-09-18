import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceKlt
import KltDP.Geometry.FrobeniusNullImagePrime
import KltDP.Examples.FrobeniusCanonicalDiscrepancyNonpositive
import KltDP.Geometry.FrobeniusNormalFactorSingularSupport
import KltDP.Geometry.SurfaceSingularCountOfSetEquality
import KltDP.Geometry.RegularTargetCanonicalDiscrepancy

/-!
# Actual Frobenius singular-count consequences

The actual regular-target canonical-discrepancy theorem supplies the reverse
singularity inclusion. The original surface, contraction and branch curves
are retained. Compilation and literature acceptance are tracked separately.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers NormalProjectiveSurface
open FrobeniusMultiCentreCanonicalWeilRepresentatives
open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

section Universal

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree (originalLine q n a ha) = 0)
    (A : InvertibleSheaf Y.toScheme) (m : ℕ) (hm : 0 < m)
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj)

include hn hπ hbir hconnected hcriterion hm e

/-- Every original contracted image point is singular: its actual canonical
discrepancy is nonpositive, whereas a regular closed image would force it
to be strictly positive by the actual canonical differential comparison. -/
theorem nullImage_subset_singularPoints :
    π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha) ⊆ (Y.singularPoints : Set Y.Point) := by
  classical
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let source := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)
  letI : IsSmoothOfRelativeDimension 2 source.structureMorphism :=
    multiStructure_smoothTwo (q + 1) n a ha
  obtain ⟨D, hK, ⟨eD⟩, hpush, _, _, _⟩ :=
    FrobeniusDiscrepancyWitness.exists_discrepancy_witness
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  let KX := targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion
  have hcanonical : IsCanonicalWeilDivisor Y KX :=
    targetCanonicalWeil_isCanonical q n a ha hn Y π hπ hbir hconnected hcriterion
  intro y hy
  apply (Y.mem_singularPoints y).mpr
  intro hregular
  obtain ⟨hyclosed, C, _, _, hCy, _⟩ :=
    exists_contracted_prime_of_mem_nullImage q n a ha hn Y π hcriterion y hy
  have hclosed : IsClosed ({π.base C.genericPoint} : Set Y.toScheme) := by
    exact hCy.symm ▸ hyclosed
  have hregularC : RegularPoint Y.toScheme (π.base C.genericPoint) := by
    exact hCy.symm ▸ hregular
  have hpositive :=
    RegularTargetCanonicalDiscrepancy.coefficient_pos_of_regular_closed_image
      source Y π hbir hπ D eD KX hcanonical hK hpush C hclosed hregularC
  have hnonpositive := FrobeniusDiscrepancyFormula.discrepancy_coeff_nonpos
    q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e D eD hK hpush C
  exact (not_lt_of_ge hnonpositive) hpositive

/-- The actual singular set is exactly the image of the original null locus. -/
theorem singularPoints_eq_nullImage :
    (Y.singularPoints : Set Y.Point) =
      π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
        (originalLine q n a ha) := by
  letI : IsIso (π ∣_ nullImageComplement q n a ha π) :=
    isIso_restrict_nullImageComplement q n a ha hn Y π hπ hbir hconnected hcriterion
  apply Set.Subset.antisymm
  · exact singularPoints_subset_nullImage q n a ha Y π
      (nullImageComplement q n a ha π) rfl
  · exact nullImage_subset_singularPoints q n a ha hn Y π hπ hbir
      hconnected hcriterion A m hm e

end Universal

/-- The same actual original rank-one KLT contraction has exactly 2n+1
singular points. The original finite image count and its original map are
retained; the reverse singularity inclusion is derived internally above. -/
theorem exists_normal_projective_surface_rank_one_klt_exact_singular_count
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    let source := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)
    ∃ m : ℕ, 0 < m ∧ ∃ (S : NormalProjectiveSurface k)
      (π : source.toScheme ⟶ S.toScheme)
      (hπ : π ≫ S.structureMorphism = multiStructure (q + 1) n a)
      (hproper : IsProper π) (hsurj : Surjective π)
      (hbir : IsBirationalScheme π) (hc : IsIso π.c),
      letI : IsProper π := hproper
      letI : Surjective π := hsurj
      letI : IsIso π.c := hc
      (∀ (L : Type u) [Field L] (y : Spec (CommRingCat.of L) ⟶ S.toScheme),
        ConnectedSpace (pullback π y : Scheme.{u})) ∧
      ∃ (hpoints : ∀ y : S.toScheme, IsConnected (π.base ⁻¹' {y}))
        (hcriterion : ∀ C : source.PrimeCurve,
          (∃ p : Spec (CommRingCat.of k) ⟶ S.toScheme,
            C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ S.structureMorphism = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0),
      ∃ A : InvertibleSheaf S.toScheme, AmpleSerre.IsAmple A ∧
        Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj) ∧
        S.NumericalSpaceFiniteDimensional ∧ S.picardRank = 1 ∧
        IsMinimalResolution source S π ∧
        let KX := targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion
        IsKltWithCanonicalDivisor S KX ∧ IsKlt S ∧
        (S.singularPoints : Set S.Point) =
          π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
            (originalLine q n a ha) ∧
        S.singularPoints.card = 2 * n + 1 ∧ S.singularPointCount = 2 * n + 1 := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
      hcriterion, A, hA, ⟨e⟩, hlabels, hfinite, hcount, U, hU, hpre,
      hIso, hsupport, hbound, hqc, hminimal, hEx, hExfinite, hExcount,
      hdim, hrank⟩ := exists_normal_projective_surface_rank_one q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  let KX := targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion
  have hKlt : IsKltWithCanonicalDivisor S KX :=
    targetCanonicalWeil_isKltWithCanonicalDivisor q n a ha hn S π hπ hbir
      hpoints hcriterion A m hm e
  have hsing := singularPoints_eq_nullImage q n a ha hn S π hπ hbir
    hpoints hcriterion A m hm e
  have hcard : S.singularPoints.card = 2 * n + 1 :=
    (S.singularPoints_card_eq_natCard_of_set_eq _ hsing).trans hcount
  exact ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
    hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal,
    hKlt, ⟨KX, hKlt⟩, hsing, hcard, hcard⟩

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.nullImage_subset_singularPoints
#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.singularPoints_eq_nullImage
#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_rank_one_klt_exact_singular_count
