import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.Basic

/-!
# Original affine localization covers and pinned scheme smoothness

The affine ring maps below are the actual appLE maps of the given morphism.
Each localization is transported to the structure sheaf on the very same
basic open. The spanning sections cover the original affine neighborhood.

The final conversion is conditional on actual standard-smooth localization
covers. It does not assert that such covers follow from algebraic smoothness;
that separate published source is not admitted in this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineSmoothLocalizationTransport

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Algebraically smooth affine neighborhoods of the original point and
original morphism, using the actual ring map rather than pinned IsSmooth. -/
def algebraSmoothAt (x : X) : Prop :=
  ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
    (e : V.1 ≤ f ⁻¹ᵁ U.1),
    letI : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U V e).hom.toAlgebra
    Algebra.Smooth Γ(Y, U.1) Γ(X, V.1)

/-- Standard smoothness on a canonical localization gives standard
smoothness of the original map on that exact geometric basic open. -/
theorem standardSmooth_appLE_basicOpen
    (U : Y.Opens) (V : X.Opens) (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (r : Γ(X, V))
    (hr : RingHom.IsStandardSmooth
      ((algebraMap Γ(X, V) (Localization.Away r)).comp (f.appLE U V e).hom)) :
    RingHom.IsStandardSmooth
      (f.appLE U (X.basicOpen r) ((X.basicOpen_le r).trans e)).hom := by
  letI : IsLocalization.Away r Γ(X, X.basicOpen r) := hV.isLocalization_basicOpen r
  let eR : Localization.Away r ≃ₐ[Γ(X, V)] Γ(X, X.basicOpen r) :=
    IsLocalization.algEquiv (Submonoid.powers r) _ _
  have he : algebraMap Γ(X, V) Γ(X, X.basicOpen r) =
      eR.toRingHom.comp (algebraMap Γ(X, V) (Localization.Away r)) := by
    ext a
    exact (eR.commutes a).symm
  rw [← f.appLE_map e (homOfLE (X.basicOpen_le r)).op]
  change RingHom.IsStandardSmooth
    ((algebraMap Γ(X, V) Γ(X, X.basicOpen r)).comp (f.appLE U V e).hom)
  rw [he, RingHom.comp_assoc]
  exact RingHom.isStandardSmooth_respectsIso.left _ eR.toRingEquiv hr

/-- A section from the given spanning family supplies the original
point with an actual standard-smooth basic-open neighborhood. -/
theorem exists_basicOpen_standardSmooth
    (U : Y.Opens) (V : X.Opens) (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V)
    (s : Set Γ(X, V)) (hs : Ideal.span s = ⊤)
    (hstd : ∀ r ∈ s, RingHom.IsStandardSmooth
      ((algebraMap Γ(X, V) (Localization.Away r)).comp (f.appLE U V e).hom)) :
    ∃ r ∈ s, x ∈ X.basicOpen r ∧ RingHom.IsStandardSmooth
      (f.appLE U (X.basicOpen r) ((X.basicOpen_le r).trans e)).hom := by
  have hcover : (⨆ r ∈ s, X.basicOpen r) = V :=
    iSup_basicOpen_of_span_eq_top V s hs
  have hx' : x ∈ (⨆ r ∈ s, X.basicOpen r) := hcover.symm ▸ hx
  obtain ⟨r, hr, hxr⟩ : ∃ r ∈ s, x ∈ X.basicOpen r := by simpa using hx'
  exact ⟨r, hr, hxr, standardSmooth_appLE_basicOpen f U V hV e r (hstd r hr)⟩

/-- Actual affine localization covers give the pinned smoothness predicate
on the same morphism. No replacement morphism or scheme is introduced. -/
theorem isSmooth_of_affine_localization_covers
    (h : ∀ x : X, ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
      (e : V.1 ≤ f ⁻¹ᵁ U.1) (s : Set Γ(X, V.1)),
      Ideal.span s = ⊤ ∧ ∀ r ∈ s, RingHom.IsStandardSmooth
        ((algebraMap Γ(X, V.1) (Localization.Away r)).comp (f.appLE U V e).hom)) :
    IsSmooth f := by
  constructor
  intro x
  obtain ⟨U, V, hx, e, s, hs, hstd⟩ := h x
  obtain ⟨r, _, hxr, hr⟩ :=
    exists_basicOpen_standardSmooth f U V V.2 e x hx s hs hstd
  exact ⟨U, ⟨X.basicOpen r, V.2.basicOpen r⟩, hxr,
    (X.basicOpen_le r).trans e, hr⟩

/-- The native affine-smooth neighborhoods convert to pinned IsSmooth
once their actual ring maps have the stated localization covers. -/
theorem isSmooth_of_algebraSmoothAt_of_localization_covers
    (h : ∀ x : X, algebraSmoothAt f x)
    (hcover : ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (letI : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U V e).hom.toAlgebra
       Algebra.Smooth Γ(Y, U.1) Γ(X, V.1)) →
      ∃ s : Set Γ(X, V.1), Ideal.span s = ⊤ ∧ ∀ r ∈ s,
        RingHom.IsStandardSmooth
          ((algebraMap Γ(X, V.1) (Localization.Away r)).comp (f.appLE U V e).hom)) :
    IsSmooth f := by
  apply isSmooth_of_affine_localization_covers f
  intro x
  obtain ⟨U, V, hx, e, hsm⟩ := h x
  obtain ⟨s, hs, hstd⟩ := hcover U V e hsm
  exact ⟨U, V, hx, e, s, hs, hstd⟩

end KltDP.Geometry.AffineSmoothLocalizationTransport

#check @KltDP.Geometry.AffineSmoothLocalizationTransport.standardSmooth_appLE_basicOpen
#print axioms KltDP.Geometry.AffineSmoothLocalizationTransport.standardSmooth_appLE_basicOpen
#check @KltDP.Geometry.AffineSmoothLocalizationTransport.isSmooth_of_algebraSmoothAt_of_localization_covers
#print axioms KltDP.Geometry.AffineSmoothLocalizationTransport.isSmooth_of_algebraSmoothAt_of_localization_covers

