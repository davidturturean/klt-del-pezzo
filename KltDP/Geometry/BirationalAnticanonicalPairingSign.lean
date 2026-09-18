import KltDP.Geometry.CanonicalWeilBirationalRepresentative
import KltDP.Geometry.BirationalCartierIntersectionPullback
import KltDP.Geometry.BirationalAmplePullbackPositiveSquare

/-!
# The original anticanonical ample numerator has negative canonical pairing

An actual target canonical Weil divisor has an exactly compatible source
Cartier representative. The original finite-Weil projection formula and
the positive square of the original ample pullback determine the sign.
The conclusion uses the chosen source canonical line and original Picard
pullback; neither a discrepancy equation nor a negative pairing is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalAnticanonicalPairingSign

open NormalProjectiveSurface SmoothCanonicalCartierRepresentative
open BirationalCartierIntersectionPullback

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hbir : IsBirationalScheme π)
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)

include hπ hbir

/-- The actual canonical class pairs negatively with the pullback of a positive
ample Cartier numerator of the original negative canonical Weil divisor. -/
theorem canonical_picardPairing_pullback_neg
    (KX : X.WeilDivisor) (hKX : IsCanonicalWeilDivisor X KX)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.cartierToWeilHom A = n • (-KX))
    (hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A)) :
    S.picardPairing hS
        (cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism))
        (schemePicardPullbackHom π (cartierPicardClass X.toScheme A)) < 0 := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  let P := DominantCartierPullback.pullbackHom π A
  obtain ⟨KS, ⟨eKS⟩, hpush⟩ :=
    IsCanonicalWeilDivisor.exists_compatible_canonical_cartier S X π hπ hbir KX hKX
  have hpos : 0 < S.intersectionPairing hS P P :=
    BirationalAmplePullbackPositiveSquare.intersectionPairing_signedPullback_pos
      π hbir hS A hample
  have hscale : S.intersectionPairing hS P P =
      -(n : ℤ) * S.intersectionPairing hS KS P := by
    rw [intersectionPairing_eq_cartierWeilRestrictionDegree S hS P P,
      cartierWeilRestrictionDegree_pullback π hπ hbir A,
      BirationalWeilPushforward.pushforward_cartier_pullback π hbir A, hA,
      map_nsmul, map_neg, nsmul_eq_mul,
      intersectionPairing_eq_cartierWeilRestrictionDegree S hS KS P,
      cartierWeilRestrictionDegree_pullback π hπ hbir A, hpush]
    ring
  have hnegative : S.intersectionPairing hS KS P < 0 := by
    have hnZ : (0 : ℤ) < n := Nat.cast_pos.mpr hn
    have hm : (n : ℤ) * S.intersectionPairing hS KS P < 0 := by
      rw [hscale] at hpos
      linarith
    by_contra h
    exact (not_lt_of_ge (mul_nonneg hnZ.le (le_of_not_gt h))) hm
  have hcanonical : cartierPicardClass S.toScheme KS =
      cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) :=
    cartierPicardClass_eq_of_iso S.toScheme KS (cartierRepresentative S.structureMorphism)
      (eKS ≪≫ (SmoothCanonicalCartierExterior.representativeIsoExterior S.structureMorphism).symm)
  have hpull : schemePicardPullbackHom π (cartierPicardClass X.toScheme A) =
      cartierPicardClass S.toScheme P := by
    exact (schemePicardPullbackHom_toPic π (cartierDivisorInvertibleSheaf X.toScheme A)).trans
      (SchemeKernelIdealIsoTransport.toPic_eq_of_iso
        (pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme A))
        (cartierDivisorInvertibleSheaf S.toScheme P)
        (DominantCartierPullback.modulePullbackIso π A))
  rw [hpull, ← hcanonical, S.picardPairing_class]
  exact hnegative

end KltDP.Geometry.BirationalAnticanonicalPairingSign

#print axioms KltDP.Geometry.BirationalAnticanonicalPairingSign.canonical_picardPairing_pullback_neg
