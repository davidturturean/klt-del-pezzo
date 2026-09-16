import KltDP.Compatibility.SmoothNoetherianFlat
import KltDP.Compatibility.StandardSmoothEtaleCoordinates
import KltDP.Compatibility.FiniteTypeMaximalHeight
import KltDP.Compatibility.ClosedAlgebraResidue
import KltDP.Compatibility.StandardSmoothLocalDimension

/-!
# A dimension lower bound at actual closed standard-smooth points

The actual polynomial coordinate map of a standard-smooth algebra is
formally smooth and of finite type. The Noetherian smooth-flat theorem
therefore makes that same map flat, so it satisfies going down. The
contraction of an actual maximal ideal is maximal: it is the kernel of
the original closed-point character composed with the coordinate map.

The proved polynomial maximal-height theorem now transfers the relative
dimension to the height of the original maximal ideal. The canonical
localized cotangent computation gives the resulting lower bound for the
Krull dimension of the original prime localization. No regularity or
dimension equality is an input to either theorem.
-/

noncomputable section

universe u

namespace KltDP.Compatibility

variable (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]

/-- The relative dimension of the actual standard-smooth algebra is at
most the height of each of its actual maximal ideals. -/
theorem standardSmooth_relativeDimension_le_maximal_height
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k A]
    (m : Ideal A) [m.IsMaximal] : (n : ℕ∞) ≤ m.height := by
  letI : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  obtain ⟨g, hg⟩ :=
    KltDP.StandardSmoothCoordinates.exists_standardSmoothZero_mvPolynomial n k A
  let B := MvPolynomial (Fin n) k
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 B A := hg
  letI : Algebra.IsStandardSmooth B A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
  letI : Module.Flat B A :=
    SmoothNoetherianFlat.formallySmooth_flat_of_finiteType
  let c : B →ₐ[k] k := (closedPointCharacter k m).comp g
  have hc : Function.Surjective c := by
    intro a
    exact ⟨algebraMap k B a, by simpa using c.commutes a⟩
  have hker : RingHom.ker c.toRingHom = m.under B := by
    ext b
    change closedPointCharacter k m (g b) = 0 ↔ algebraMap B A b ∈ m
    exact closedPointCharacter_eq_zero_iff k m (g b)
  have hm : (m.under B).IsMaximal :=
    hker ▸ RingHom.ker_isMaximal_of_surjective c hc
  have hpoly : (n : ℕ∞) ≤ (m.under B).height :=
    polynomial_maximal_height_ge k n (m.under B) hm
  have hheight : (n : ℕ∞) ≤ m.primeHeight :=
    nat_le_primeHeight_of_hasGoingDown B A n m
      (by simpa only [Ideal.height_eq_primeHeight] using hpoly)
  simpa only [Ideal.height_eq_primeHeight] using hheight

/-- At an actual closed standard-smooth point over the original
algebraically closed field, the cotangent dimension is at most the Krull
dimension of its actual localization. -/
theorem standardSmooth_closed_cotangent_finrank_le_ringKrullDim
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n k A]
    (m : Ideal A) [m.IsMaximal] :
    (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
      (IsLocalRing.CotangentSpace (Localization.AtPrime m)) : WithBot ℕ∞) ≤
        ringKrullDim (Localization.AtPrime m) := by
  letI : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  letI := closedResidueField_formallyEtale k m
  rw [finrank_cotangent_localization_of_standardSmooth
    k A (Localization.AtPrime m) m.primeCompl n,
    IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  exact WithBot.coe_le_coe.mpr
    (standardSmooth_relativeDimension_le_maximal_height k A n m)

end KltDP.Compatibility
