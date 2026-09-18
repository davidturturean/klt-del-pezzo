import KltDP.Geometry.AffineStalkCompletion
import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.ResolutionConstructionRemainingInputs

/-!
# Conditional completion normality at original singular points

The complete proposed closed-point statement of Zariski's Theorem 2 is
an explicit argument, quantified over all original fields and affine
coordinate algebras. It is not asserted or hidden behind a source predicate.

Each actual singular point is closed. Its actual affine section algebra,
maximal ideal, prime localization and stalk completion are used unchanged.
The original completion equivalence transports all three ring conclusions.
The final consumers keep the existing modification and contraction inputs
explicit; no initial resolution or contraction existence is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry

variable (hZariski :
  ∀ (k : Type u) [Field k]
    (B : Type u) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B]
    (p : Ideal B) [p.IsMaximal]
    [IsIntegrallyClosed (Localization.AtPrime p)],
    IsLocalRing
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)) ∧
      IsDomain
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)) ∧
      IsIntegrallyClosed
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)))

variable {k : Type u} [Field k]

include hZariski

/-- The original singular-point stalk completion is local, a domain and
integrally closed, conditional on the entire explicit closed-point source. -/
theorem localCompletion_singularStalk_normal_of_zariski
    (X : NormalProjectiveSurface k) (x : X.Point)
    (hx : x ∈ singularLocus X.toScheme) :
    IsLocalRing (localCompletion (X.toScheme.presheaf.stalk x)) ∧
      IsDomain (localCompletion (X.toScheme.presheaf.stalk x)) ∧
      IsIntegrallyClosed (localCompletion (X.toScheme.presheaf.stalk x)) := by
  let U : X.toScheme.Opens := (X.toScheme.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.toScheme.affineCover.map x)
  let xu : U := ⟨x, X.toScheme.affineCover.covers x⟩
  letI : Nonempty U := ⟨xu⟩
  letI : Algebra Γ(X.toScheme, U) (X.toScheme.presheaf.stalk x) :=
    X.toScheme.presheaf.algebra_section_stalk xu
  letI : Algebra Γ(X.toScheme, U) (localCompletion (X.toScheme.presheaf.stalk x)) :=
    inferInstance
  letI : Algebra k Γ(X.toScheme, U) := affineSectionsAlgebra X.structureMorphism hU
  letI : Algebra.FiniteType k Γ(X.toScheme, U) :=
    affineSectionsAlgebra_finiteType X.structureMorphism hU
  letI : (hU.primeIdealOf xu).asIdeal.IsMaximal :=
    isMaximal_primeIdealOf_of_isClosed X.toScheme hU xu
      (singularPoint_isClosed X x hx)
  letI : IsIntegrallyClosed (Localization.AtPrime (hU.primeIdealOf xu).asIdeal) :=
    ((affineStalkLocalization_normal_iff hU xu).mpr (X.normal x)).2
  have hcompleted := hZariski k Γ(X.toScheme, U) (hU.primeIdealOf xu).asIdeal
  have hnormal := (affineStalkCompletion_normal_iff hU xu).mp hcompleted.2
  letI : IsDomain (localCompletion (X.toScheme.presheaf.stalk x)) := hnormal.1
  letI : IsLocalRing
      (AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime (hU.primeIdealOf xu).asIdeal))
        (Localization.AtPrime (hU.primeIdealOf xu).asIdeal)) := hcompleted.1
  have hlocal : IsLocalRing (localCompletion (X.toScheme.presheaf.stalk x)) :=
    IsLocalRing.of_surjective' (affineStalkCompletionAlgEquiv hU xu).toRingHom
      (affineStalkCompletionAlgEquiv hU xu).surjective
  exact ⟨hlocal, hnormal⟩

variable [IsAlgClosed k]

/-- The explicit Zariski source discharges completion normality in the
current conditional raw modification input. Projectivity and dimension of
the original integral resolution source are supplied by proved adapters. -/
theorem lipmanResolutionLiteral_of_zariski
    (hL : LipmanModificationLiteral k) : LipmanResolutionLiteral k := by
  constructor
  intro X hfin
  obtain ⟨S, π, hS, hreg, hπ, hbir⟩ :=
    hL.exists_resolution X hfin
      (fun x hx => (localCompletion_singularStalk_normal_of_zariski hZariski X x hx).2)
  letI : IsIntegral S := hS
  letI : IsProper π := hπ
  letI : IsProper X.structureMorphism := X.projective.isProper
  have hdim : topologicalKrullDim S = 2 :=
    (topologicalKrullDim_eq_of_proper_birational π X.structureMorphism hbir).trans
      X.dimension_two
  exact ⟨regularProperSurface S (π ≫ X.structureMorphism) hreg hdim, π,
    regularProperSurface_isResolution X S π hreg hdim hbir⟩

/-- The actual minimal resolution follows conditionally from the full
explicit Zariski source and the remaining modification/contraction inputs.
The finite singular locus and exceptional-prime termination are proved. -/
theorem exists_minimalResolution_of_zariski_and_remaining_inputs
    (hL : LipmanModificationLiteral k)
    (hCa : CastelnuovoContractionLiteral k) (hU : ContractionUniversalLiteral k)
    (X : NormalProjectiveSurface k) :
    ∃ (S : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
      IsMinimalResolution S X π := by
  obtain ⟨S, π, hπ⟩ := (lipmanResolutionLiteral_of_zariski hZariski hL).exists_resolution
    X (normalSurface_singularLocus_finite X)
  exact hπ.exists_minimalResolution_of_contraction_inputs hCa hU

end KltDP.Geometry
