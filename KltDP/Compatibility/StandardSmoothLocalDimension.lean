import KltDP.Compatibility.SmoothLocalCotangent
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Cotangent dimension on an actual localization of a standard-smooth algebra

The standard-smooth presentation gives the rank of its actual Kähler module.
The pinned formally-étale comparison transports that module to a localization.
The actual cotangent-space comparison then computes the local embedding
dimension, provided the actual residue extension is formally étale.

All algebra structures and their scalar tower remain explicit. In particular,
no Krull-dimension equality or regularity conclusion is assumed here.
-/

noncomputable section

open TensorProduct

universe u

namespace KltDP.Compatibility

/-- Localization preserves the dimension of the actual Kähler module of a
standard-smooth algebra. Nontriviality of the original ring follows from
the actual localization map to the nontrivial target. -/
theorem finrank_kaehler_localization_of_standardSmooth
    (k A T : Type u) [CommRing k] [CommRing A] [CommRing T]
    [Algebra k A] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
    [Nontrivial T] (M : Submonoid A) [IsLocalization M T]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k A] :
    Module.finrank T (Ω[T⁄k]) = n := by
  letI : Nontrivial A := (algebraMap A T).domain_nontrivial
  letI : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  letI : Algebra.FormallyEtale A T := Algebra.FormallyEtale.of_isLocalization M
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A T
  calc
    Module.finrank T (Ω[T⁄k]) = Module.finrank T (T ⊗[A] Ω[A⁄k]) :=
      e.finrank_eq.symm
    _ = Module.finrank A (Ω[A⁄k]) := Module.finrank_baseChange
    _ = n := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
        (R := k) (S := A) n)

/-- At an actual local localization, a formally étale residue extension
identifies the standard-smooth relative dimension with the dimension of
the actual maximal-ideal cotangent space. -/
theorem finrank_cotangent_localization_of_standardSmooth
    (k A T : Type u) [CommRing k] [CommRing A] [CommRing T] [IsLocalRing T]
    [Algebra k A] [Algebra k T] [Algebra A T] [IsScalarTower k A T]
    (M : Submonoid A) [IsLocalization M T]
    [Algebra.FormallyEtale k (IsLocalRing.ResidueField T)]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k A] :
    Module.finrank (IsLocalRing.ResidueField T) (IsLocalRing.CotangentSpace T) = n := by
  letI : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  letI : Algebra.FormallyEtale A T := Algebra.FormallyEtale.of_isLocalization M
  letI : Algebra.FormallySmooth k T := Algebra.FormallySmooth.comp k A T
  letI : Module.Free T (Ω[T⁄k]) := Module.Free.of_equiv
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A T)
  rw [finrank_cotangentSpace_eq_finrank_kaehler k T]
  exact finrank_kaehler_localization_of_standardSmooth k A T M n

end KltDP.Compatibility
