import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Completion along an algebra equivalence

An algebra equivalence carrying the original ideal onto the target ideal
induces an algebra equivalence of their actual adic completions. The map
is defined on every original quotient in the compatible-family model.
Its value on the canonical image of the original ring is retained.
-/

noncomputable section

namespace KltDP.Geometry

section IdealCompletion

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- Coefficient transport on the actual quotient used by adic completion. -/
def adicQuotientAlgEquiv (e : A ≃ₐ[R] B) (I : Ideal A) (J : Ideal B)
    (hIJ : J = I.map e.toRingHom) (n : ℕ) :
    (A ⧸ (I ^ n • ⊤ : Ideal A)) ≃ₐ[R] B ⧸ (J ^ n • ⊤ : Ideal B) :=
  Ideal.quotientEquivAlg _ _ e (by
    simpa only [smul_eq_mul, Ideal.mul_top, Ideal.map_pow] using
      congrArg (fun K : Ideal B => K ^ n) hIJ)

/-- Quotient transport commutes with the original transition maps. -/
theorem adicQuotientAlgEquiv_transition (e : A ≃ₐ[R] B)
    (I : Ideal A) (J : Ideal B) (hIJ : J = I.map e.toRingHom)
    {m n : ℕ} (hmn : m ≤ n) (a : A ⧸ (I ^ n • ⊤ : Ideal A)) :
    AdicCompletion.transitionMap J B hmn (adicQuotientAlgEquiv e I J hIJ n a) =
      adicQuotientAlgEquiv e I J hIJ m (AdicCompletion.transitionMap I A hmn a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- The algebra equivalence induced on the original compatible families. -/
def adicCompletionAlgEquiv (e : A ≃ₐ[R] B) (I : Ideal A) (J : Ideal B)
    (hIJ : J = I.map e.toRingHom) :
    AdicCompletion I A ≃ₐ[R] AdicCompletion J B where
  toFun a := ⟨fun n => adicQuotientAlgEquiv e I J hIJ n (a.val n), by
    intro m n hmn
    rw [adicQuotientAlgEquiv_transition, a.property hmn]⟩
  invFun b := ⟨fun n => (adicQuotientAlgEquiv e I J hIJ n).symm (b.val n), by
    intro m n hmn
    apply (adicQuotientAlgEquiv e I J hIJ m).injective
    rw [← adicQuotientAlgEquiv_transition]
    simpa only [AlgEquiv.apply_symm_apply] using b.property hmn⟩
  left_inv a := AdicCompletion.ext fun n =>
    (adicQuotientAlgEquiv e I J hIJ n).symm_apply_apply (a.val n)
  right_inv b := AdicCompletion.ext fun n =>
    (adicQuotientAlgEquiv e I J hIJ n).apply_symm_apply (b.val n)
  map_mul' a b := AdicCompletion.ext fun n =>
    (adicQuotientAlgEquiv e I J hIJ n).map_mul (a.val n) (b.val n)
  map_add' a b := AdicCompletion.ext fun n =>
    (adicQuotientAlgEquiv e I J hIJ n).map_add (a.val n) (b.val n)
  commutes' r := AdicCompletion.ext fun n =>
    (adicQuotientAlgEquiv e I J hIJ n).commutes r

/-- The completion equivalence extends the given original algebra map. -/
@[simp]
theorem adicCompletionAlgEquiv_of (e : A ≃ₐ[R] B)
    (I : Ideal A) (J : Ideal B) (hIJ : J = I.map e.toRingHom) (a : A) :
    adicCompletionAlgEquiv e I J hIJ (AdicCompletion.of I A a) =
      AdicCompletion.of J B (e a) := by
  apply AdicCompletion.ext
  intro n
  rfl

end IdealCompletion

section MaximalIdealCompletion

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [IsLocalRing A] [IsLocalRing B]

/-- The target maximal ideal is the image of the original maximal ideal. -/
theorem maximalIdeal_eq_map_algEquiv (e : A ≃ₐ[R] B) :
    IsLocalRing.maximalIdeal B = (IsLocalRing.maximalIdeal A).map e.toRingHom := by
  have h : ((IsLocalRing.maximalIdeal A).map e.toRingHom).IsMaximal :=
    Ideal.map_isMaximal_of_equiv e
  exact (IsLocalRing.eq_maximalIdeal h).symm

/-- Completion transport for the maximal ideals of the original local rings. -/
def maximalIdealCompletionAlgEquiv (e : A ≃ₐ[R] B) :
    AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[R]
      AdicCompletion (IsLocalRing.maximalIdeal B) B :=
  adicCompletionAlgEquiv e _ _ (maximalIdeal_eq_map_algEquiv e)

@[simp]
theorem maximalIdealCompletionAlgEquiv_of (e : A ≃ₐ[R] B) (a : A) :
    maximalIdealCompletionAlgEquiv e
        (AdicCompletion.of (IsLocalRing.maximalIdeal A) A a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal B) B (e a) :=
  adicCompletionAlgEquiv_of e _ _ _ a

end MaximalIdealCompletion

end KltDP.Geometry
