import KltDP.Geometry.Surface
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Sober

/-!
# Nonempty integral projective space

The homogeneous zero prime is an actual point of projective space: a
nonzero degree-one coordinate lies in the irrelevant ideal. This point is
dense, so the underlying space is irreducible. Each actual structure-sheaf
stalk embeds, through its homogeneous-localization description, into an
ordinary prime localization of the polynomial domain. Thus every stalk is
a domain, and projective space is reduced and integral.

These results concern the existing `Proj` scheme and its existing structure
morphism. Normality and the dimension-two theorem needed for a complete
`NormalProjectiveSurface` witness remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- A homogeneous prime localization of a domain is a domain via its actual
injective inclusion into the ordinary prime localization. -/
theorem homogeneousLocalizationAtPrime_isDomain {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [IsDomain A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (P : Ideal A) [P.IsPrime] :
    IsDomain (HomogeneousLocalization.AtPrime 𝒜 P) := by
  letI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_of_local_atPrime (inferInstance : P.IsPrime)
  exact Function.Injective.isDomain
    (algebraMap (HomogeneousLocalization.AtPrime 𝒜 P) (Localization.AtPrime P))
    (HomogeneousLocalization.val_injective (𝒜 := 𝒜) P.primeCompl)

/-- Actual Proj stalks of a graded domain are domains. The equivalence used
here is the structure sheaf's existing stalk-localization equivalence. -/
theorem proj_stalk_isDomain {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [IsDomain A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (x : Proj 𝒜) : IsDomain ((Proj 𝒜).presheaf.stalk x) := by
  letI : IsDomain (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
    homogeneousLocalizationAtPrime_isDomain 𝒜 x.asHomogeneousIdeal.toIdeal
  exact MulEquiv.isDomain
    (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)
    (Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv.toMulEquiv

/-- Reducedness of the actual Proj scheme follows from its domain stalks. -/
theorem proj_isReduced_of_isDomain {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [IsDomain A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    IsReduced (Proj 𝒜) := by
  letI (x : Proj 𝒜) : IsDomain ((Proj 𝒜).presheaf.stalk x) := proj_stalk_isDomain 𝒜 x
  exact isReduced_of_isReduced_stalk (Proj 𝒜)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous zero prime gives an actual point of projective space.
A coordinate variable proves that this prime does not contain the irrelevant
ideal, including when `n = 0`. -/
def projectiveSpaceZeroPrime (k : Type u) [Field k] (n : ℕ) :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k)).IsPrime
    exact Ideal.bot_prime
  not_irrelevant_le := by
    intro h
    have hx :
        (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ∈
          HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 1)))
        (by decide : (1 : ℕ) ≠ 0)
    have hz :
        (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ∈
          (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k)) := h hx
    exact MvPolynomial.X_ne_zero (R := k) (0 : Fin (n + 1)) (Ideal.mem_bot.mp hz)

/-- The zero homogeneous prime is a concrete witness that the existing
projective-space scheme is nonempty. -/
theorem projectiveSpace_nonempty (k : Type u) [Field k] (n : ℕ) :
    Nonempty (projectiveSpace k n) :=
  ⟨projectiveSpaceZeroPrime k n⟩

/-- The closure of the homogeneous zero prime is all of projective space. -/
theorem closure_projectiveSpaceZeroPrime (k : Type u) [Field k] (n : ℕ) :
    closure ({projectiveSpaceZeroPrime k n} : Set (projectiveSpace k n)) = Set.univ := by
  change closure ({projectiveSpaceZeroPrime k n} :
    Set (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))) = Set.univ
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton]
  change ProjectiveSpectrum.zeroLocus
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
      ((⊥ : Ideal (MvPolynomial (Fin (n + 1)) k)) :
        Set (MvPolynomial (Fin (n + 1)) k)) = Set.univ
  exact ProjectiveSpectrum.zeroLocus_bot _

/-- The actual projective-space scheme is irreducible because its zero
homogeneous prime is a dense generic point. -/
theorem projectiveSpace_irreducibleSpace (k : Type u) [Field k] (n : ℕ) :
    IrreducibleSpace (projectiveSpace k n) := by
  apply (irreducibleSpace_def _).mpr
  have hη : IsGenericPoint (projectiveSpaceZeroPrime k n)
      (Set.univ : Set (projectiveSpace k n)) := closure_projectiveSpaceZeroPrime k n
  exact hη.isIrreducible

/-- Every structure-sheaf stalk of actual projective space is a domain. -/
theorem projectiveSpace_stalk_isDomain (k : Type u) [Field k] (n : ℕ)
    (x : projectiveSpace k n) : IsDomain ((projectiveSpace k n).presheaf.stalk x) :=
  proj_stalk_isDomain (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) x

/-- The existing projective-space scheme is integral. This does not yet
assert that it has dimension `n` or that its stalks are integrally closed. -/
theorem projectiveSpace_isIntegral (k : Type u) [Field k] (n : ℕ) :
    IsIntegral (projectiveSpace k n) := by
  letI : IrreducibleSpace (projectiveSpace k n) := projectiveSpace_irreducibleSpace k n
  letI : IsReduced (projectiveSpace k n) :=
    proj_isReduced_of_isDomain (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
  exact isIntegral_of_irreducibleSpace_of_isReduced (projectiveSpace k n)

/-- The identity embedding establishes projectivity over the original
structure morphism, with no separate assumed projectivity result. -/
theorem projectiveSpace_isProjectiveOverField (k : Type u) [Field k] (n : ℕ) :
    IsProjectiveOverField (projectiveSpaceToSpec k n) :=
  ⟨n, 𝟙 (projectiveSpace k n), inferInstance, Category.id_comp _⟩

end KltDP.Geometry
