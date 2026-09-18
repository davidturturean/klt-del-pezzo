import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceSequenceDiscrepancy
import KltDP.Geometry.SmoothProjectiveDiscrepancyDescent

/-!
# The original Frobenius contraction on every smooth projective birational model

Retain the original constructor and its finite point-blowup conclusions.
The actual common-model descent gives the literal discrepancy bound for
every independently chosen canonical Cartier divisor with exact pushforward
to the same target canonical divisor. No all-normal-model or KLT claim occurs.
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

/-- The same original Frobenius rank-one target has the strict discrepancy
bound for every smooth projective birational model and every actual
canonical Cartier representative pushing to its fixed canonical divisor. -/
theorem exists_normal_projective_surface_rank_one_discrepancy_all_smooth_models
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
            (∀ (T : NormalProjectiveSurface k) (f : T.toScheme ⟶ source.toScheme)
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
                  QCartierPullback.pullback (f ≫ π) (rationalizeWeilDivisor S KX) hK) C) ∧
            ∀ (V : NormalProjectiveSurface k) (_ : IsSmooth V.structureMorphism)
              (v : V.toScheme ⟶ S.toScheme) [hvproper : IsProper v]
              (hv : IsBirationalScheme v)
              (_ : v ≫ S.structureMorphism = V.structureMorphism)
              (KV : CartierDivisor V.toScheme),
              (cartierDivisorModule V.toScheme KV ≅
                relativeDifferentialExterior V.structureMorphism 2) →
              BirationalWeilPushforward.pushforward v hv (V.cartierToWeilHom KV) = KX →
              letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
              ∀ C : V.PrimeCurve, (-1 : ℚ) < (V.rationalCartierToWeilHom KV -
                QCartierPullback.pullback v (rationalizeWeilDivisor S KX) hK) C := by
  classical
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
      hpoints, hcriterion, A, hA, he, hdim, hrank, hminimal,
      hcanonical, D, hK, heD, hpush, hbound, E, hsnc, hEWeil, hseq⟩ :=
    exists_normal_projective_surface_rank_one_discrepancy_all_point_blowups q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let source := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)
  letI : IsSmoothOfRelativeDimension 2 source.structureMorphism :=
    multiStructure_smoothTwo (q + 1) n a ha
  let KX := targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion
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
  have heD' : Nonempty (cartierDivisorModule source.toScheme D ≅
      relativeDifferentialExterior source.structureMorphism 2) := heD
  refine ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
    hpoints, hcriterion, A, hA, he, hdim, hrank, hminimal,
    hcanonical, D, hK, heD', hpush, hbound, E, hsnc, hEWeil', hseq, ?_⟩
  intro V hV v hvproper hv hvk KV eKV hpushV
  letI : IsSmooth V.structureMorphism := hV
  letI : IsProper v := hvproper
  have hcompat : BirationalWeilPushforward.pushforward v hv (V.cartierToWeilHom KV) =
      BirationalWeilPushforward.pushforward π hbir (source.cartierToWeilHom D) :=
    hpushV.trans hpush.symm
  exact canonical_discrepancy_gt_neg_one_on_smooth_projective_model
    source S π hbir hπ D (Classical.choice heD')
    (rationalizeWeilDivisor S KX) hK E hsnc hcoeff hsupport hbound
    V V.isSmoothOfRelativeDimension_two v hv hvk KV eKV hcompat

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

#check @KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_rank_one_discrepancy_all_smooth_models
#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_rank_one_discrepancy_all_smooth_models
