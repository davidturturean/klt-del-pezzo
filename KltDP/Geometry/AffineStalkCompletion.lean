import KltDP.Geometry.AdicCompletionAlgebraEquiv
import KltDP.Geometry.ProjectiveChartNormal
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The original affine local ring and its stalk completion

An affine neighborhood identifies its original prime localization with
the structure-sheaf stalk. Completing this algebra equivalence identifies
the actual maximal-ideal completions and retains the original germ map.
The normality statements below are equivalences under these actual maps;
they do not assert analytic normality or assume an excellence theorem.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)

/-- The original affine prime localization is the original stalk as an
algebra over the original section ring. -/
def affineStalkLocalizationAlgEquiv :
    Localization.AtPrime (hU.primeIdealOf x).asIdeal ≃ₐ[Γ(X, U)] X.presheaf.stalk x := by
  letI := hU.isLocalization_stalk x
  exact IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl _ _

/-- The localization equivalence preserves the original section germ. -/
@[simp]
theorem affineStalkLocalizationAlgEquiv_algebraMap (a : Γ(X, U)) :
    affineStalkLocalizationAlgEquiv hU x
        (algebraMap Γ(X, U) (Localization.AtPrime (hU.primeIdealOf x).asIdeal) a) =
      X.presheaf.germ U x x.property a :=
  (affineStalkLocalizationAlgEquiv hU x).commutes a

/-- Local normality is unchanged by the actual affine localization map. -/
theorem affineStalkLocalization_normal_iff :
    (IsDomain (Localization.AtPrime (hU.primeIdealOf x).asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime (hU.primeIdealOf x).asIdeal)) ↔
    (IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) := by
  let e := (affineStalkLocalizationAlgEquiv hU x).toRingEquiv
  constructor
  · rintro ⟨hD, hN⟩
    letI := hD
    letI := hN
    exact ⟨MulEquiv.isDomain _ e.symm.toMulEquiv, isIntegrallyClosed_of_ringEquiv e⟩
  · rintro ⟨hD, hN⟩
    letI := hD
    letI := hN
    exact ⟨MulEquiv.isDomain _ e.toMulEquiv, isIntegrallyClosed_of_ringEquiv e.symm⟩

/-- The actual maximal-ideal completion of the affine prime localization
is the actual maximal-ideal completion of the structure-sheaf stalk. -/
def affineStalkCompletionAlgEquiv :
    AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime (hU.primeIdealOf x).asIdeal))
        (Localization.AtPrime (hU.primeIdealOf x).asIdeal) ≃ₐ[Γ(X, U)]
      AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) :=
  maximalIdealCompletionAlgEquiv (affineStalkLocalizationAlgEquiv hU x)

/-- Completion transport extends the actual localization-to-stalk map. -/
@[simp]
theorem affineStalkCompletionAlgEquiv_of
    (a : Localization.AtPrime (hU.primeIdealOf x).asIdeal) :
    affineStalkCompletionAlgEquiv hU x
        (AdicCompletion.of
          (IsLocalRing.maximalIdeal (Localization.AtPrime (hU.primeIdealOf x).asIdeal))
          (Localization.AtPrime (hU.primeIdealOf x).asIdeal) a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) (affineStalkLocalizationAlgEquiv hU x a) :=
  maximalIdealCompletionAlgEquiv_of (affineStalkLocalizationAlgEquiv hU x) a

/-- On an original section, the completed map is its original germ
followed by the original stalk completion map. -/
@[simp]
theorem affineStalkCompletionAlgEquiv_algebraMap (a : Γ(X, U)) :
    affineStalkCompletionAlgEquiv hU x
        (AdicCompletion.of
          (IsLocalRing.maximalIdeal (Localization.AtPrime (hU.primeIdealOf x).asIdeal))
          (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
          (algebraMap Γ(X, U) (Localization.AtPrime (hU.primeIdealOf x).asIdeal) a)) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) (X.presheaf.germ U x x.property a) := by
  rw [affineStalkCompletionAlgEquiv_of, affineStalkLocalizationAlgEquiv_algebraMap]

/-- Normality of either actual completion is equivalent to normality of
the other, without changing the original affine neighborhood or point. -/
theorem affineStalkCompletion_normal_iff :
    (IsDomain (AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime (hU.primeIdealOf x).asIdeal))
        (Localization.AtPrime (hU.primeIdealOf x).asIdeal)) ∧
      IsIntegrallyClosed (AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime (hU.primeIdealOf x).asIdeal))
        (Localization.AtPrime (hU.primeIdealOf x).asIdeal))) ↔
    (IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x))) := by
  let e := (affineStalkCompletionAlgEquiv hU x).toRingEquiv
  constructor
  · rintro ⟨hD, hN⟩
    letI := hD
    letI := hN
    exact ⟨MulEquiv.isDomain _ e.symm.toMulEquiv, isIntegrallyClosed_of_ringEquiv e⟩
  · rintro ⟨hD, hN⟩
    letI := hD
    letI := hN
    exact ⟨MulEquiv.isDomain _ e.toMulEquiv, isIntegrallyClosed_of_ringEquiv e.symm⟩

end KltDP.Geometry
