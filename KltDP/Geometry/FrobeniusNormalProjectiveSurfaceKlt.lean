import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceSmoothModelDiscrepancy
import KltDP.Geometry.NormalModelKltOfSNC

/-!
# The original Frobenius contraction is KLT on all normal models

The universal statement applies to every original positive-power contraction
with its proved connectedness and curve-contraction criterion. Its actual
canonical representative and discrepancy are constructed internally. The
actual reduced support is SNC, so the all-normal-model criterion applies.

The existence theorem retains the same original source, target, morphism,
ample positive power, connected fibers, rank and minimal resolution.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers NormalProjectiveSurface
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreCanonicalWeilRepresentatives
open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

/-- Every original positive-power Frobenius contraction is KLT with respect
to its actual chosen target canonical divisor. No discrepancy data or
normal-model comparison is assumed: all of it is derived from the map. -/
theorem targetCanonicalWeil_isKltWithCanonicalDivisor
    {k : Type u} [Field k] [IsAlgClosed k]
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
    (e : (pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj) :
    IsKltWithCanonicalDivisor Y
      (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) := by
  classical
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let hproj := originalMultiStructureProjective k (q + 1) n a
  let source := sourceSurface q n a ha hproj
  letI : IsSmoothOfRelativeDimension 2 source.structureMorphism :=
    multiStructure_smoothTwo (q + 1) n a ha
  letI : IsSmooth source.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 source.structureMorphism
  obtain ⟨D, hK, ⟨eD⟩, hpush, hformula, hbound, _⟩ :=
    FrobeniusDiscrepancyWitness.exists_discrepancy_witness
      q n a ha hn Y π hπ hbir hconnected hcriterion A m hm e
  let KX := targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion
  have hcanonical : IsCanonicalWeilDivisor Y KX :=
    targetCanonicalWeil_isCanonical q n a ha hn Y π hπ hbir hconnected hcriterion
  let Δ : source.RationalWeilDivisor := source.rationalCartierToWeilHom D -
    QCartierPullback.pullback π (rationalizeWeilDivisor Y KX) hK
  have hformula' : Δ = FrobeniusDiscrepancyBounds.candidate q n a ha hproj := hformula
  let E : CartierDivisor source.toScheme :=
    FrobeniusDiscrepancyBounds.candidateSupportCartier q n a ha hproj
  have hsnc : IsStrictNormalCrossingsCartier source.toScheme E :=
    FrobeniusDiscrepancyBounds.candidateSupportCartier_isStrictNormalCrossings q n a ha hproj
  have hEWeil : source.cartierToWeilHom E = source.selectedPrimeWeil Δ.support :=
    (FrobeniusDiscrepancyBounds.candidateSupportCartier_weil q n a ha hproj).trans
      (congrArg (fun B : source.RationalWeilDivisor => source.selectedPrimeWeil B.support)
        hformula'.symm)
  have hcoeff : ∀ C : source.PrimeCurve,
      source.cartierToWeilHom E C = 0 ∨ source.cartierToWeilHom E C = 1 := by
    intro C
    rw [hEWeil, source.selectedPrimeWeil_apply]
    by_cases hC : C ∈ Δ.support <;> simp [hC]
  have hsupport : Δ.support ⊆ (source.cartierToWeilHom E).support := by
    have hs : Δ.support ⊆ Δ.support := fun _ h => h
    simpa only [hEWeil, source.selectedPrimeWeil_support] using hs
  exact isKltWithCanonicalDivisor_of_snc_discrepancy source Y π hbir hπ D eD
    KX hcanonical hK hpush E hsnc hcoeff hsupport hbound

/-- The actual original rank-one construction has KLT singularities on all
normal models, with its map, ample positive power and minimal resolution. -/
theorem exists_normal_projective_surface_rank_one_klt
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
        IsKltWithCanonicalDivisor S KX ∧ IsKlt S := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
      hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal,
      _, _⟩ :=
    exists_normal_projective_surface_rank_one_discrepancy_all_smooth_models q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  let KX := targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion
  have hKlt : IsKltWithCanonicalDivisor S KX :=
    targetCanonicalWeil_isKltWithCanonicalDivisor q n a ha hn S π hπ hbir
      hpoints hcriterion A m hm e
  exact ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
    hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal, hKlt, ⟨KX, hKlt⟩⟩

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

#check @KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.targetCanonicalWeil_isKltWithCanonicalDivisor
#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.targetCanonicalWeil_isKltWithCanonicalDivisor
#check @KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_rank_one_klt
#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_rank_one_klt
