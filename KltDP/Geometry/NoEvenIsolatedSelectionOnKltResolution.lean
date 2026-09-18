import KltDP.Geometry.EvenIsolatedSelectionBlowdownNumerics
import KltDP.Geometry.OriginalCoverAnticanonicalNefSign
import KltDP.Geometry.NegativeCanonicalBlowdownInvariants
import KltDP.Geometry.EvenSelectionIrregularityCancellation
import KltDP.Geometry.KltResolutionNegativeCanonical
import KltDP.Geometry.KltResolutionPicardRank

/-!
# No nonempty even isolated minus-two selection on an original klt del Pezzo resolution

The original Picard half-class constructs one cover and one ramification
blowdown with its complete retained forest. The actual anticanonical ample
class gives the cover's negative canonical nef pairing. The derived native
invariants, transported through that same blowdown, force exactly the rank
which the full retained forest proves strictly too small.

The actual source and target H1 terms cancel through the computed Euler
formula. No rationality, cohomology vanishing, Euler, canonical-square,
rank-drop, classification, or target-matrix formula is assumed.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence
open ModuleCohomology SmoothCanonicalCartierRepresentative SmoothCanonicalExteriorComparison
open OriginalCartierRamificationSmooth

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}

local instance noEvenKltResolutionSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance noEvenKltResolutionMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- An actual nonempty even isolated minus-two selection is impossible on
the specified original minimal resolution of a rank-one klt del Pezzo surface. -/
theorem no_nonempty_even_isolatedSelection_of_klt_resolution
    (π : S.toScheme ⟶ X.toScheme) (hmin : IsMinimalResolution S X π)
    (hDP : IsKltDelPezzo X) (hrankX : X.picardRank = 1)
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (N : Finset S.PrimeCurve) (hiso : IsolatedSelection π N)
    (hN : ∀ A ∈ N, IsExceptionalCurve π A) (hneN : N.Nonempty)
    (hself : ∀ A ∈ N, A.selfIntersectionNumber hmin.regular = -2)
    (m : Additive S.toScheme.Pic)
    (heven : letI : IsSmooth S.structureMorphism :=
      MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
      S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) = (2 : ℕ) • m)
    (h2 : IsUnit (2 : k)) : False := by
  letI : IsProper π := hmin.toIsResolution.isProper
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  have hbir : IsBirationalScheme π := (isBirational_iff_isBirationalScheme π).mp hmin.birational
  have hklt : IsKlt X := by
    obtain ⟨KX, hKX, _⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
    exact ⟨KX, hKX⟩
  let KS := cartierRepresentative S.structureMorphism
  have eKS : cartierDivisorModule S.toScheme KS ≅ relativeDifferentialExterior S.structureMorphism 2 :=
    SmoothCanonicalCartierExterior.representativeIsoExterior S.structureMorphism
  have hsource := hmin.toIsResolution.noether_euler_relations_of_kltDelPezzo hDP KS eKS
  have hSourceRank : S.picardRank = Nat.card (Vertices π) + 1 := by
    have h := hmin.picardRank_eq_of_klt hklt p hp
    rw [hrankX] at h
    omega
  obtain ⟨E, hE, L, e, hIJ, hred, hne, hweil, _hL, hfamily⟩ :=
    exists_evenSelection_forest_blowdown_with_numerics
      π N hbir hmin hklt hiso hN hneN hself m heven h2
  obtain ⟨V, hV, b, Q, _hcard, _hdrop, hseq, _hcontract, _hQ, _hmatrix,
    _hcount, _hspan, hbound, hEuler, KT, ⟨eKT⟩, hSquare⟩ := hfamily
  let Y := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
  let hY := MinimalResolutionQuadraticRegular.selectedCover_regularPoints
    π hmin E hE L e h2 hred hne N hIJ (isolatedSelection_pairwise π N hiso hN)
    (selectedExceptional_isSmooth π N hmin hklt hN)
  letI : IsSmoothOfRelativeDimension 1
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) :=
    isolatedSelection_canonicalBranch_isSmoothOne π N hmin hklt hiso hN E hE hIJ
  letI : IsIntegral Y.toScheme := Y.integral
  letI : IsSmoothOfRelativeDimension 2 Y.structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  let KY := cartierRepresentative Y.structureMorphism
  have eKY : cartierDivisorModule Y.toScheme KY ≅ relativeDifferentialExterior Y.structureMorphism 2 :=
    SmoothCanonicalCartierExterior.representativeIsoExterior Y.structureMorphism
  obtain ⟨_KX, _hKX, _n, A, _hn, _hA, _hample, _hnefS, hnefY, _hnegativeS, hnegativeY⟩ :=
    exists_anticanonical_nef_with_cover_canonical_negative
      π N hbir hmin hklt hiso hN E hE L e h2 hred hne hIJ hweil hDP
  have htarget := hseq.target_invariants_of_negative_nef hY hV KY KT eKY eKT _ hnefY hnegativeY
  have hRank : V.picardRank = 2 * (Nat.card (Vertices π) - N.card) :=
    EvenSelectionIrregularityCancellation.target_rank_eq_twice_complement
      (Nat.card (Vertices π)) N.card S.picardRank V.picardRank
      (S.intersectionPairing hmin.regular KS KS) (V.intersectionPairing hV KT KT)
      (eulerCharacteristic S.structureMorphism (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf))
      (eulerCharacteristic V.structureMorphism (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf))
      (cohomologyDimension S.structureMorphism (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1)
      (cohomologyDimension V.structureMorphism (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) 1)
      hEuler hsource.2 htarget.2 hsource.1 hSourceRank hSquare htarget.1
  exact (not_lt_of_ge hRank.le) hbound

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.no_nonempty_even_isolatedSelection_of_klt_resolution
