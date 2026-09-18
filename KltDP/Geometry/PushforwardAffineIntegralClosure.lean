import KltDP.Geometry.PushforwardAffineDiagram
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Original integral closure on every affine base open

The pinned universally-closed global-section theorem applies to the
original restriction of the map. Cancelling the actual restriction-ring
isomorphism proves integrality of the original `f.app U`, without a
Noetherian assumption. The actual integral-closure subalgebra is thus the
whole original pushforward ring on each affine base open.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.PushforwardAffineIntegralClosure

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The literal section map over an original affine open is integral. -/
theorem app_isIntegral [UniversallyClosed f] (U : Y.AffineZariskiSite) :
    (f.app U.1).hom.IsIntegral := by
  letI : IsAffine U.1.toScheme := U.2
  letI : UniversallyClosed (f ∣_ U.1) :=
    IsLocalAtTarget.restrict (P := @UniversallyClosed) inferInstance U.1
  have h := isIntegral_appTop_of_universallyClosed (f ∣_ U.1)
  rw [morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.isIntegral_respectsIso.cancel_right_isIso] at h
  have h : (f.app (U.1.ι ''ᵁ ⊤)).hom.IsIntegral := h
  rwa [Scheme.Opens.ι_image_top] at h

/-- The actual integral-closure subalgebra in the original inverse-image section ring. -/
def closure (U : Y.AffineZariskiSite) :
    letI := (f.app U.1).hom.toAlgebra
    Subalgebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := by
  letI := (f.app U.1).hom.toAlgebra
  exact integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)

/-- For a universally closed map, every original pushforward section is integral. -/
theorem closure_eq_top [UniversallyClosed f] (U : Y.AffineZariskiSite) :
    letI := (f.app U.1).hom.toAlgebra
    closure f U = ⊤ := by
  letI := (f.app U.1).hom.toAlgebra
  exact integralClosure_eq_top_iff.mpr ⟨app_isIntegral f U⟩

/-- The original integral-closure inclusion, promoted to an algebra isomorphism. -/
def closureEquiv [UniversallyClosed f] (U : Y.AffineZariskiSite) :
    letI := (f.app U.1).hom.toAlgebra
    closure f U ≃ₐ[Γ(Y, U.1)] Γ(X, f ⁻¹ᵁ U.1) := by
  letI := (f.app U.1).hom.toAlgebra
  exact (Subalgebra.equivOfEq _ _ (closure_eq_top f U)).trans Subalgebra.topEquiv

@[simp] theorem closureEquiv_apply [UniversallyClosed f] (U : Y.AffineZariskiSite) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ x : closure f U, closureEquiv f U x = x.val := by
  letI := (f.app U.1).hom.toAlgebra
  intro x
  rfl

end KltDP.Geometry.PushforwardAffineIntegralClosure
