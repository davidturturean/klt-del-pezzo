import KltDP.Geometry.RegularProperSurface
import KltDP.Geometry.ProperBirationalDimension
import KltDP.Geometry.ActualResolutionExceptionalCount

/-!
# Remove proved auxiliary inputs from the resolution construction

The existing raw modification and completion predicates remain explicit,
unproved source inputs. Projectivity and dimension are derived for the
original integral regular proper source, using the selected isolated
Hartshorne projectivity theorem and the proved birational dimension theorem.

Minimalization uses the actual number of exceptional primes, whose strict
decrease has already been proved. Its two remaining contraction inputs are
kept explicit. This file admits no literature statement and does not assert
unconditional existence of a resolution or of a contraction.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Literature.Stacks
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The original raw resolution source acquires projectivity and dimension
internally. Only the still-unproved modification/completion inputs remain. -/
theorem lipmanResolutionLiteral_of_remaining_inputs
    (hL : LipmanModificationLiteral k)
    (hE : FiniteTypeExcellentFormalFibresLiteral k)
    (hC : CompletionNormalLiteral.{u}) : LipmanResolutionLiteral k := by
  constructor
  intro X hfin
  obtain ⟨S, π, hS, hreg, hπ, hbir⟩ :=
    hL.exists_resolution X hfin (fun x _ => localCompletion_stalk_normal hE hC X x)
  letI : IsIntegral S := hS
  letI : IsProper π := hπ
  letI : IsProper X.structureMorphism := X.projective.isProper
  have hdim : topologicalKrullDim S = 2 :=
    (topologicalKrullDim_eq_of_proper_birational π X.structureMorphism hbir).trans
      X.dimension_two
  exact ⟨regularProperSurface S (π ≫ X.structureMorphism) hreg hdim, π,
    regularProperSurface_isResolution X S π hreg hdim hbir⟩

/-- Starting from an actual resolution, finite exceptional-prime induction
needs only existence and descent of its actual exceptional contractions. -/
theorem IsResolution.exists_minimalResolution_of_contraction_inputs
    (hCa : CastelnuovoContractionLiteral k) (hU : ContractionUniversalLiteral k)
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hπ : IsResolution S X π) :
    ∃ (S' : NormalProjectiveSurface k) (π' : S'.toScheme ⟶ X.toScheme),
      IsMinimalResolution S' X π' := by
  suffices key : ∀ (n : ℕ) (T : NormalProjectiveSurface k) (f : T.toScheme ⟶ X.toScheme),
      IsResolution T X f → {C : T.PrimeCurve | IsExceptionalCurve f C}.ncard = n →
        ∃ (T' : NormalProjectiveSurface k) (f' : T'.toScheme ⟶ X.toScheme),
          IsMinimalResolution T' X f' from
    key _ S π hπ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T f hf hn
    by_cases hmin : ∀ C : T.PrimeCurve, IsExceptionalCurve f C →
        ¬ IsMinusOneCurve hf.regular C
    · exact ⟨T, f, { toIsResolution := hf, no_minusOne_curve := hmin }⟩
    · push_neg at hmin
      obtain ⟨E, hE, hE1⟩ := hmin
      obtain ⟨T', b, hb⟩ := hCa.exists_contraction T hf.regular E hE1
      obtain ⟨f', hfac, hres⟩ := hf.of_contraction hU hb hE
      refine ih _ ?_ T' f' hres rfl
      rw [← hn]
      exact hb.ncard_exceptionalCurves_lt_of_actualMaps hf hres hfac hE

/-- The remaining source boundary is explicit: modification, normal
completion, contraction existence, and contraction descent. No projectivity,
dimension, dense-open or termination hypothesis is supplied. -/
theorem exists_minimalResolution_of_remaining_inputs
    (hL : LipmanModificationLiteral k)
    (hE : FiniteTypeExcellentFormalFibresLiteral k)
    (hC : CompletionNormalLiteral.{u})
    (hCa : CastelnuovoContractionLiteral k) (hU : ContractionUniversalLiteral k)
    (X : NormalProjectiveSurface k) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsMinimalResolution S X π := by
  obtain ⟨S, π, hπ⟩ := (lipmanResolutionLiteral_of_remaining_inputs hL hE hC).exists_resolution
    X (normalSurface_singularLocus_finite X)
  exact hπ.exists_minimalResolution_of_contraction_inputs hCa hU

end KltDP.Geometry

#check @KltDP.Geometry.lipmanResolutionLiteral_of_remaining_inputs
#check @KltDP.Geometry.IsResolution.exists_minimalResolution_of_contraction_inputs
#check @KltDP.Geometry.exists_minimalResolution_of_remaining_inputs
#print axioms KltDP.Geometry.lipmanResolutionLiteral_of_remaining_inputs
#print axioms KltDP.Geometry.IsResolution.exists_minimalResolution_of_contraction_inputs
#print axioms KltDP.Geometry.exists_minimalResolution_of_remaining_inputs
