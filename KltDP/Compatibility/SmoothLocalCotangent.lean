import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The cotangent space of a formally smooth local algebra

Let `A` be a formally smooth `k`-algebra whose residue field is formally
étale over `k`. The canonical conormal map identifies the actual cotangent
space of `A` with the residue-field fiber of its Kähler differentials.
Both sides retain their original residue-field module structures.

The proof uses the conormal exact sequence and the split-injection
criterion already proved in Mathlib at commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (Apache-2.0):
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` and
`Algebra.FormallySmooth.iff_injective_and_split`. No regularity or
dimension assertion is an input to the comparison.
-/

noncomputable section

open TensorProduct

universe u

namespace KltDP.Compatibility

variable (k A : Type u) [CommRing k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Algebra.FormallySmooth k A]
    [Algebra.FormallyEtale k (IsLocalRing.ResidueField A)]

/-- The canonical conormal map, with its scalar action extended along the
actual residue quotient, is an isomorphism over the actual residue field. -/
def localCotangentEquivResidueTensor :
    IsLocalRing.CotangentSpace A ≃ₗ[IsLocalRing.ResidueField A]
      (IsLocalRing.ResidueField A) ⊗[A] Ω[A⁄k] := by
  have hsurj : Function.Surjective
      (algebraMap A (IsLocalRing.ResidueField A)) :=
    IsLocalRing.residue_surjective
  have hbij : Function.Bijective
      (KaehlerDifferential.kerCotangentToTensor k A (IsLocalRing.ResidueField A)) := by
    constructor
    · exact ((Algebra.FormallySmooth.iff_injective_and_split
        (R := k) hsurj).mp inferInstance).1
    · intro x
      exact (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
        k A (IsLocalRing.ResidueField A) hsurj x).mp (Subsingleton.elim _ _)
  have e : IsLocalRing.CotangentSpace A ≃ₗ[A]
      (IsLocalRing.ResidueField A) ⊗[A] Ω[A⁄k] := by
    have hker : RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) =
        IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
    exact Eq.mp (congrArg (fun I : Ideal A =>
      I.Cotangent ≃ₗ[A] (IsLocalRing.ResidueField A) ⊗[A] Ω[A⁄k]) hker)
      (LinearEquiv.ofBijective
        (KaehlerDifferential.kerCotangentToTensor k A (IsLocalRing.ResidueField A)) hbij)
  exact e.extendScalarsOfSurjective hsurj

/-- For free Kähler differentials, passage to the residue field preserves
their rank and computes the dimension of the actual local cotangent space. -/
theorem finrank_cotangentSpace_eq_finrank_kaehler
    [Module.Free A (Ω[A⁄k])] :
    Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) =
      Module.finrank A (Ω[A⁄k]) := by
  rw [(localCotangentEquivResidueTensor k A).finrank_eq,
    Module.finrank_baseChange]

/-- An established finite rank for the Kähler module gives the same
dimension for the local cotangent space. -/
theorem finrank_cotangentSpace_eq_of_kaehler_rank
    [Module.Free A (Ω[A⁄k])] {n : ℕ}
    (hrank : Module.rank A (Ω[A⁄k]) = n) :
    Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) = n := by
  rw [finrank_cotangentSpace_eq_finrank_kaehler k A]
  exact Module.finrank_eq_of_rank_eq hrank

end KltDP.Compatibility
