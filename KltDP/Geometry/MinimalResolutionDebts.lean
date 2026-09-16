import KltDP.Literature.ResolutionDebtLiterals
import KltDP.Geometry.MinimalResolutionExistence
import KltDP.Geometry.SurfaceFiniteness
import KltDP.Geometry.RegularLocalUFD
import KltDP.Geometry.RegularLocalEquiv
import KltDP.Geometry.AffineFiniteType
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Lipman's specialisation debts discharged, and uniqueness of the minimal resolution (F10, E2)

Consumers of the literals in `KltDP.Literature.ResolutionDebtLiterals` and `KltDP.Literature.ResolutionLiterals`.

* `localCompletion_stalk_normal`: the completion of every local ring of `X : NormalProjectiveSurface k` is normal.
  The stalk is the localization of the finite type `k`-algebra `Γ(X, U)` at a prime, for an affine open `U ∋ x`
  (`IsAffineOpen.isLocalization_stalk`, accepted `affineSectionsAlgebra_finiteType`), so excellence
  (07QW, 07QU) gives normal formal fibres and 0C23 a normal completion.
* `isNormalScheme_of_regularPoint`: regular schemes are normal (accepted factoriality of regular local rings and
  Mathlib's `UniqueFactorizationMonoid.instIsIntegrallyClosed`).
* `lipmanResolutionLiteral_of_literals`: the E1 literal `LipmanResolutionLiteral k` follows from 0BGP (4) ⇒ (2),
  excellence, 0C23, 0C5P and 02JX. The resolution scheme of 0BGP is made a `NormalProjectiveSurface k` with
  structure morphism `π ≫ X.structureMorphism`: normal (regular), projective (0C5P), dimension two (02JX).
* `exists_minimalResolution'`: every `X : NormalProjectiveSurface k` over an algebraically closed field has a
  minimal resolution. The finiteness of the singular locus is the accepted F01 theorem
  `normalSurface_singularLocus_finite`. Hypotheses: literals only, plus the E1 termination hypothesis
  `ContractionMeasureHypothesis`, which is not discharged here.
* `IsPointBlowupSequence.regular_of_regular`: sources of point-blowup sequences into a regular surface are regular
  (0AGR; isomorphisms transport regularity through stalk isomorphisms).
* `minimalResolution_unique`: two minimal resolutions of `X` are isomorphic over `X`, conditional on 0C5R, 0AGR and
  the named hypotheses `BlowupExceptionalMinusOne` and `MinimalResolutionDominationHypothesis`. The dominating
  morphism is a sequence of point blowups (0C5R); a nontrivial first blowup would contribute an exceptional
  `(−1)`-curve of the source resolution, contradicting its minimality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k]

section Debts

/-- The completion of every local ring of a normal projective surface is normal (excellence and 0C23). -/
theorem localCompletion_stalk_normal (hE : FiniteTypeExcellentFormalFibresLiteral k)
    (hC : CompletionNormalLiteral.{u}) (X : NormalProjectiveSurface k) (x : X.Point) :
    IsDomain (localCompletion (X.toScheme.presheaf.stalk x)) ∧
      IsIntegrallyClosed (localCompletion (X.toScheme.presheaf.stalk x)) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (isBasis_affine_open X.toScheme).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU' : IsAffineOpen U := hU
  letI : Algebra k Γ(X.toScheme, U) := affineSectionsAlgebra X.structureMorphism hU'
  haveI : Algebra.FiniteType k Γ(X.toScheme, U) :=
    affineSectionsAlgebra_finiteType X.structureMorphism hU'
  have hloc := hU'.isLocalization_stalk ⟨x, hxU⟩
  have hff : FormalFibresNormal (X.toScheme.presheaf.stalk x) :=
    @FiniteTypeExcellentFormalFibresLiteral.formalFibres_normal k _ hE Γ(X.toScheme, U) _ _ _
      (hU'.primeIdealOf ⟨x, hxU⟩).asIdeal _ (X.toScheme.presheaf.stalk x) _ _
      (TopCat.Presheaf.algebra_section_stalk X.toScheme.presheaf (U := U) ⟨x, hxU⟩) hloc
  exact hC.completion_normal (X.toScheme.presheaf.stalk x) inferInstance inferInstance hff

/-- A scheme regular at every point is normal. -/
theorem isNormalScheme_of_regularPoint {S : Scheme.{u}} (hreg : ∀ s : S, RegularPoint S s) :
    IsNormalScheme S := by
  intro s
  obtain ⟨hD, hU⟩ := regularPoint_stalk_isDomain_and_uniqueFactorizationMonoid S s (hreg s)
  letI : IsDomain (S.presheaf.stalk s) := hD
  haveI : UniqueFactorizationMonoid (S.presheaf.stalk s) := hU
  exact ⟨hD, UniqueFactorizationMonoid.instIsIntegrallyClosed⟩

/-- **The specialisation debts of `LipmanResolutionLiteral`, discharged by literals.** -/
theorem lipmanResolutionLiteral_of_literals (hL : LipmanModificationLiteral k)
    (hE : FiniteTypeExcellentFormalFibresLiteral k) (hC : CompletionNormalLiteral.{u})
    (hP : RegularProperProjectiveLiteral k) (hD : BirationalDimensionLiteral k) :
    LipmanResolutionLiteral k := by
  refine ⟨fun X hfin => ?_⟩
  obtain ⟨S, π, hS, hreg, hπ, hbir⟩ :=
    hL.exists_resolution X hfin (fun x _ => localCompletion_stalk_normal hE hC X x)
  haveI : IsProper X.structureMorphism := X.projective.isProper
  have hdim : topologicalKrullDim S = 2 := (hD.dim_eq X S π hπ hbir).trans X.dimension_two
  refine ⟨⟨S, π ≫ X.structureMorphism, hS, isNormalScheme_of_regularPoint hreg,
    hP.projective S (π ≫ X.structureMorphism) inferInstance hreg hdim, hdim⟩, π, rfl, hreg, ?_⟩
  exact ⟨hbir.map_genericPoint, hbir.isIso_stalkMap_genericPoint⟩

/-- **Existence of a minimal resolution** of every normal projective surface over an algebraically closed field,
from the Stacks literals (0BGP, 07QW/07QU, 0C23, 0C5P, 02JX, 0C2N, 0C5J) and the E1 termination hypothesis. -/
theorem exists_minimalResolution' [IsAlgClosed k]
    (hL : LipmanModificationLiteral k) (hE : FiniteTypeExcellentFormalFibresLiteral k)
    (hC : CompletionNormalLiteral.{u}) (hP : RegularProperProjectiveLiteral k)
    (hD : BirationalDimensionLiteral k) (hCa : CastelnuovoContractionLiteral k)
    (hU : ContractionUniversalLiteral k) (hμ : ContractionMeasureHypothesis k)
    (X : NormalProjectiveSurface k) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme), IsMinimalResolution S X π :=
  exists_minimalResolution (lipmanResolutionLiteral_of_literals hL hE hC hP hD) hCa hU hμ X
    (normalSurface_singularLocus_finite X)

end Debts

section Uniqueness

/-- The source of a sequence of point blowups into a regular surface is regular (0AGR). -/
theorem IsPointBlowupSequence.regular_of_regular (hR : BlowupRegularLiteral k)
    {S T : NormalProjectiveSurface k} {f : S.toScheme ⟶ T.toScheme}
    (h : IsPointBlowupSequence S T f) :
    (∀ t : T.Point, RegularPoint T.toScheme t) → ∀ s : S.Point, RegularPoint S.toScheme s := by
  induction h with
  | of_isIso g hg _ =>
    intro hT s
    haveI := hg
    exact regularLocal_of_ringEquiv (asIso (g.stalkMap s)).commRingCatIsoToRingEquiv (hT (g.base s))
  | step b g x' hb _ ih =>
    intro hT
    exact hR.regular _ _ b x' hb (ih hT)

/-- **Uniqueness of the minimal resolution** (manuscript "its minimal resolution", Prop. 2.4), conditional on
0C5R, 0AGR and the named hypotheses `BlowupExceptionalMinusOne`, `MinimalResolutionDominationHypothesis`. -/
theorem minimalResolution_unique [IsAlgClosed k]
    (hF : BirationalFactorizationLiteral k) (hR : BlowupRegularLiteral k)
    (hE : BlowupExceptionalMinusOne k) (hDom : MinimalResolutionDominationHypothesis k)
    {S₁ S₂ X : NormalProjectiveSurface k} {π₁ : S₁.toScheme ⟶ X.toScheme}
    {π₂ : S₂.toScheme ⟶ X.toScheme} (h₁ : IsMinimalResolution S₁ X π₁)
    (h₂ : IsMinimalResolution S₂ X π₂) :
    ∃ e : S₂.toScheme ≅ S₁.toScheme, e.hom ≫ π₁ = π₂ := by
  obtain ⟨f, hfac, hbir⟩ := hDom.dominates S₁ X π₁ h₁ S₂ π₂ h₂.toIsResolution
  have hover : f ≫ S₁.structureMorphism = S₂.structureMorphism := by
    rw [← h₁.over_base, ← Category.assoc, hfac, h₂.over_base]
  have hseq := hF.factor S₂ S₁ f h₂.regular h₁.regular hover hbir
  clear hover hbir
  cases hseq with
  | of_isIso _ hg _ =>
    haveI := hg
    exact ⟨asIso f, hfac⟩
  | step b g x' hb hg =>
    exfalso
    subst hfac
    have hS' := hg.regular_of_regular hR h₁.regular
    obtain ⟨E, hE1, hEimg⟩ := hE.exists_minusOne S₂ _ b x' hb hS' h₂.regular
    have hExc : IsExceptionalCurve ((b ≫ g) ≫ π₁) E := by
      show ∃ y : X.Point, ((b ≫ g) ≫ π₁).base '' (E : Set S₂.toScheme) = {y}
      refine ⟨(g ≫ π₁).base x', ?_⟩
      calc ((b ≫ g) ≫ π₁).base '' (E : Set S₂.toScheme)
          = (g ≫ π₁).base '' (b.base '' (E : Set S₂.toScheme)) := by
            rw [Set.image_image]
            exact Set.image_congr (fun s _ => by simp only [Scheme.comp_base_apply])
        _ = {(g ≫ π₁).base x'} := by rw [hEimg, Set.image_singleton]
    exact h₂.no_minusOne_curve E hExc hE1

end Uniqueness

end KltDP.Geometry
