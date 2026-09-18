import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceDiscrepancySNC
import KltDP.Geometry.PointBlowupSequenceDiscrepancyPushforward
import KltDP.Geometry.FrobeniusTargetIsCanonical

/-!
# The original Frobenius contraction on every finite point-blowup model

Extract the original rank-one contraction once. Its actual source canonical
Cartier divisor and reduced discrepancy support feed the proved finite
point-blowup induction. Composition preserves the same target canonical
Weil divisor. This is a finite-sequence discrepancy statement, not a KLT claim.
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

/- Keep the general sequence argument opaque before instantiating it with the
original Frobenius surface. This avoids expanding that surface's construction
inside the finite-sequence induction and its pushforward calculation. -/
private theorem discrepancy_all_point_blowups_of_reduced_support
    {k : Type u} [Field k] [IsAlgClosed k]
    (source S : NormalProjectiveSurface k) [IsSmooth source.structureMorphism]
    (π : source.toScheme ⟶ S.toScheme) [IsProper π] [GenericPointPreserving π]
    (hbir : IsBirationalScheme π) (KX : S.WeilDivisor)
    (D : CartierDivisor source.toScheme)
    (eD : cartierDivisorModule source.toScheme D ≅
      relativeDifferentialExterior source.structureMorphism 2)
    (hK : S.QCartier (rationalizeWeilDivisor S KX))
    (hpush : BirationalWeilPushforward.pushforward π hbir
      (source.cartierToWeilHom D) = KX)
    (E : CartierDivisor source.toScheme)
    (hsnc : IsStrictNormalCrossingsCartier source.toScheme E)
    (hEWeil : source.cartierToWeilHom E = source.selectedPrimeWeil
      (source.rationalCartierToWeilHom D -
        QCartierPullback.pullback π (rationalizeWeilDivisor S KX) hK).support)
    (hbound : ∀ C : source.PrimeCurve, (-1 : ℚ) < (source.rationalCartierToWeilHom D -
      QCartierPullback.pullback π (rationalizeWeilDivisor S KX) hK) C) :
    ∀ (T : NormalProjectiveSurface k) (f : T.toScheme ⟶ source.toScheme)
      (hf : IsPointBlowupSequence T source f),
      letI : GenericPointPreserving f := hf.genericPointPreserving
      letI : IsProper f := hf.isProper
      ∃ (KT ET : CartierDivisor T.toScheme),
        Nonempty (cartierDivisorModule T.toScheme KT ≅
          relativeDifferentialExterior T.structureMorphism 2) ∧
        BirationalWeilPushforward.pushforward (f ≫ π)
            (BirationalWeilPushforward.comp_isBirational f hf.isBirationalScheme π hbir)
            (T.cartierToWeilHom KT) = KX ∧
        IsStrictNormalCrossingsCartier T.toScheme ET ∧
        (∀ C : T.PrimeCurve,
          T.cartierToWeilHom ET C = 0 ∨ T.cartierToWeilHom ET C = 1) ∧
        (T.rationalCartierToWeilHom KT -
          QCartierPullback.pullback (f ≫ π) (rationalizeWeilDivisor S KX) hK).support ⊆
            (T.cartierToWeilHom ET).support ∧
        ∀ C : T.PrimeCurve, (-1 : ℚ) < (T.rationalCartierToWeilHom KT -
          QCartierPullback.pullback (f ≫ π) (rationalizeWeilDivisor S KX) hK) C := by
  classical
  let Δ : source.RationalWeilDivisor := source.rationalCartierToWeilHom D -
    QCartierPullback.pullback π (rationalizeWeilDivisor S KX) hK
  have hEWeil' : source.cartierToWeilHom E = source.selectedPrimeWeil Δ.support := hEWeil
  have hcoeff : ∀ C : source.PrimeCurve,
      source.cartierToWeilHom E C = 0 ∨ source.cartierToWeilHom E C = 1 := by
    intro C
    rw [hEWeil', source.selectedPrimeWeil_apply]
    by_cases hC : C ∈ Δ.support <;> simp [hC]
  have hsupport : Δ.support ⊆ (source.cartierToWeilHom E).support := by
    have hs : Δ.support ⊆ Δ.support := fun _ h => h
    simpa only [hEWeil', source.selectedPrimeWeil_support] using hs
  intro T f hf
  letI : GenericPointPreserving f := hf.genericPointPreserving
  letI : IsProper f := hf.isProper
  obtain ⟨KT, ET, heKT, hpushT, hET, hcoeffT, hsupportT, hboundT⟩ :=
    hf.exists_canonical_discrepancy_boundary_with_pushforward
      π D eD (rationalizeWeilDivisor S KX) hK E hsnc hcoeff hsupport hbound
  refine ⟨KT, ET, heKT, ?_, hET, hcoeffT, hsupportT, hboundT⟩
  calc
    BirationalWeilPushforward.pushforward (f ≫ π)
        (BirationalWeilPushforward.comp_isBirational f hf.isBirationalScheme π hbir)
        (T.cartierToWeilHom KT) =
      BirationalWeilPushforward.pushforward π hbir
        (BirationalWeilPushforward.pushforward f hf.isBirationalScheme (T.cartierToWeilHom KT)) :=
      BirationalWeilPushforward.pushforward_comp f hf.isBirationalScheme π hbir _
    _ = BirationalWeilPushforward.pushforward π hbir (source.cartierToWeilHom D) :=
      congrArg (BirationalWeilPushforward.pushforward π hbir) hpushT
    _ = KX := hpush

/-- The actual Frobenius constructor has canonical discrepancy coefficients
strictly greater than minus one on every original finite point-blowup model,
with exact canonical pushforward to its original chosen target divisor. -/
theorem exists_normal_projective_surface_rank_one_discrepancy_all_point_blowups
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
        letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
        let KX := targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion
        IsCanonicalWeilDivisor S KX ∧
        ∃ (D : CartierDivisor source.toScheme)
          (hK : S.QCartier (rationalizeWeilDivisor S KX)),
          Nonempty (cartierDivisorModule source.toScheme D ≅
            relativeDifferentialExterior source.structureMorphism 2) ∧
          BirationalWeilPushforward.pushforward π hbir (source.cartierToWeilHom D) = KX ∧
          let Δ := source.rationalCartierToWeilHom D -
            QCartierPullback.pullback π (rationalizeWeilDivisor S KX) hK
          (∀ C : source.PrimeCurve, (-1 : ℚ) < Δ C) ∧
          ∃ E : CartierDivisor source.toScheme,
            IsStrictNormalCrossingsCartier source.toScheme E ∧
            source.cartierToWeilHom E = source.selectedPrimeWeil Δ.support ∧
            ∀ (T : NormalProjectiveSurface k) (f : T.toScheme ⟶ source.toScheme)
              (hf : IsPointBlowupSequence T source f),
              letI : GenericPointPreserving f := hf.genericPointPreserving
              letI : IsProper f := hf.isProper
              ∃ (KT ET : CartierDivisor T.toScheme),
                Nonempty (cartierDivisorModule T.toScheme KT ≅
                  relativeDifferentialExterior T.structureMorphism 2) ∧
                BirationalWeilPushforward.pushforward (f ≫ π)
                    (BirationalWeilPushforward.comp_isBirational f hf.isBirationalScheme π hbir)
                    (T.cartierToWeilHom KT) = KX ∧
                IsStrictNormalCrossingsCartier T.toScheme ET ∧
                (∀ C : T.PrimeCurve,
                  T.cartierToWeilHom ET C = 0 ∨ T.cartierToWeilHom ET C = 1) ∧
                (T.rationalCartierToWeilHom KT -
                  QCartierPullback.pullback (f ≫ π) (rationalizeWeilDivisor S KX) hK).support ⊆
                    (T.cartierToWeilHom ET).support ∧
                ∀ C : T.PrimeCurve, (-1 : ℚ) < (T.rationalCartierToWeilHom KT -
                  QCartierPullback.pullback (f ≫ π) (rationalizeWeilDivisor S KX) hK) C := by
  classical
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
      hcriterion, A, hA, he, hlabels, hfinite, hcount, U, hU, hpre,
      hIso, hsingular, hcard, hqc, hminimal, hEx, hExfinite, hExcount,
      hdim, hrank, D, hK, heD, hpush, hformula, hbound, hold,
      E, hE, hsnc, hEWeil, hradical, hsupportIdeal⟩ :=
    exists_normal_projective_surface_rank_one_discrepancy_snc q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let source := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)
  letI : IsSmoothOfRelativeDimension 2 (multiStructure (q + 1) n a) :=
    multiStructure_smoothTwo (q + 1) n a ha
  letI : IsSmooth source.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 (multiStructure (q + 1) n a)
  let KX := targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion
  have hcanonical : IsCanonicalWeilDivisor S KX :=
    targetCanonicalWeil_isCanonical q n a ha hn S π hπ hbir hpoints hcriterion
  let Δ : source.RationalWeilDivisor := source.rationalCartierToWeilHom D -
    QCartierPullback.pullback π (rationalizeWeilDivisor S KX) hK
  have hEWeil' : source.cartierToWeilHom E = source.selectedPrimeWeil Δ.support := hEWeil
  have heD' : Nonempty (cartierDivisorModule source.toScheme D ≅
      relativeDifferentialExterior source.structureMorphism 2) := heD
  have hseq := discrepancy_all_point_blowups_of_reduced_support source S π hbir KX
    D (Classical.choice heD') hK hpush E hsnc hEWeil' hbound
  exact ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
    hpoints, hcriterion, A, hA, he, hdim, hrank, hminimal,
    hcanonical, D, hK, heD', hpush, hbound, E, hsnc, hEWeil', hseq⟩

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

#check @KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_rank_one_discrepancy_all_point_blowups
#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_rank_one_discrepancy_all_point_blowups
