/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

The derivative helper is adapted from Mathlib/Algebra/MvPolynomial/PDeriv.lean:
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Yury Kudryashov
-/
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Actual étale coordinates from a standard-smooth presentation

This bounded port reuses the constructive proof in official Mathlib commit
5315eef9e4ffb98e0f89f278b765c50a149f66ca, RingTheory/RingHom/StandardSmooth.lean,
`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`.
The old pin bundles the variable and relation types in the presentation;
we retain those actual types and construct the new presentation explicitly.

The endpoint retains the stronger dimension-zero standard-smooth condition
on the actual polynomial-algebra map. Pinned Mathlib then supplies its actual
étale algebra instance. No theorem about the chosen point's fiber, flatness,
or a smooth surface's dimension is assumed here.
-/

noncomputable section

open MvPolynomial

namespace KltDP.StandardSmoothCoordinates

universe u v

/-- The derivative comparison used in the upstream coordinate proof,
obtained directly from the pinned evaluation-and-derivative theorem. -/
private theorem pderiv_sumAlgEquiv
    {R σ ι : Type*} [CommRing R] (i : σ) (p : MvPolynomial (σ ⊕ ι) R) :
    pderiv i (sumAlgEquiv R σ ι p) =
      sumAlgEquiv R σ ι (pderiv (Sum.inl i) p) := by
  change pderiv i
      (MvPolynomial.aeval (Sum.elim MvPolynomial.X
        (MvPolynomial.C ∘ (MvPolynomial.X : ι → MvPolynomial ι R))) p) = _
  exact (MvPolynomial.aeval_sumElim_pderiv_inl p
    (MvPolynomial.X : ι → MvPolynomial ι R) i).symm

/-- An actual standard-smooth algebra of relative dimension `n` receives
an actual polynomial-algebra map whose relative dimension is zero.
The scalar action in the conclusion is precisely the action induced by
that map, not an unrelated algebra instance. -/
theorem exists_standardSmoothZero_mvPolynomial
    (n : ℕ) (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ g : MvPolynomial (Fin n) R →ₐ[R] S,
      @Algebra.IsStandardSmoothOfRelativeDimension 0
        (MvPolynomial (Fin n) R) S _ _ g.toRingHom.toAlgebra := by
  classical
  obtain ⟨P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (R := R) (S := S) (n := n)
  letI := Fintype.ofFinite P.vars
  letI := Fintype.ofFinite P.rels
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set P.vars) = n := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
    simpa only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] using hP
  let ec : ((Set.range P.map)ᶜ : Set P.vars) ≃ Fin n := Fintype.equivFinOfCardEq hc
  let e₀ : P.rels ⊕ Fin n ≃ P.vars :=
    ((Equiv.ofInjective P.map P.map_inj).sumCongr ec.symm).trans
      (Equiv.Set.sumCompl (Set.range P.map))
  have he₀ (i : P.rels) : e₀ (Sum.inl i) = P.map i := rfl
  let e : MvPolynomial P.rels (MvPolynomial (Fin n) R) ≃ₐ[R] P.Ring :=
    (MvPolynomial.sumAlgEquiv R _ _).symm.trans (MvPolynomial.renameEquiv _ e₀)
  let φ := e.toAlgHom.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) _)
  algebraize [φ.toRingHom, (algebraMap P.Ring S).comp φ.toRingHom]
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) P.Ring :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) S := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap R S r =
      algebraMap P.Ring S (φ (algebraMap R (MvPolynomial (Fin n) R) r))
    rw [φ.commutes, ← IsScalarTower.algebraMap_apply R P.Ring S]
  refine ⟨IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) S, ?_⟩
  have H : (MvPolynomial.aeval
        (fun x ↦ (algebraMap P.Ring S) (e (MvPolynomial.X x)))).toRingHom =
      (algebraMap P.Ring S).comp e.toRingHom := by
    ext
    · simp [e, IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) S]
    · simp [e, @RingHom.algebraMap_toAlgebra (MvPolynomial (Fin n) R) S, φ]
    · simp [e]
  let Q : Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R) S :=
    { toGenerators := Algebra.Generators.ofSurjective
        (fun x ↦ algebraMap P.Ring S (e (MvPolynomial.X x))) (by
          intro s
          obtain ⟨p, hp⟩ := P.algebraMap_surjective s
          refine ⟨e.symm p, ?_⟩
          have he : e.toRingEquiv.toRingHom (e.symm p) = p := e.apply_symm_apply p
          exact (DFunLike.congr_fun H (e.symm p)).trans
            (by simpa only [RingHom.comp_apply, he] using hp))
      rels := P.rels
      relation := e.symm ∘ P.relation
      span_range_relation_eq_ker := by
        change Ideal.span (Set.range (e.symm ∘ P.relation)) =
          RingHom.ker (MvPolynomial.aeval
            (fun x ↦ (algebraMap P.Ring S) (e (MvPolynomial.X x)))).toRingHom
        rw [Set.range_comp, ← AlgEquiv.coe_ringEquiv e.symm, AlgEquiv.symm_toRingEquiv,
          ← Ideal.map_span, P.span_range_relation_eq_ker, Ideal.map_symm]
        change (RingHom.ker (algebraMap P.Ring S)).comap e.toRingHom = _
        rw [RingHom.comap_ker, ← H]
      map := id
      map_inj := Function.injective_id
      relations_finite := inferInstanceAs (Finite P.rels) }
  let Q' : Algebra.SubmersivePresentation (MvPolynomial (Fin n) R) S :=
    { toPreSubmersivePresentation := Q
      jacobian_isUnit := by
        convert P.jacobian_isUnit using 1
        simp_rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
          RingHom.map_det]
        congr 1
        ext i j
        trans algebraMap P.Ring S (e (pderiv i (e.symm (P.relation j))))
        · simpa [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, Q,
            Algebra.Generators.ofSurjective] using DFunLike.congr_fun H
              (pderiv i (e.symm (P.relation j)))
        suffices e (pderiv i (e.symm (P.relation j))) =
            pderiv (P.map i) (P.relation j) by
          simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, this]
        apply e.symm.injective
        rw [AlgEquiv.symm_apply_apply]
        change pderiv i (sumAlgEquiv R P.rels (Fin n)
            (rename e₀.symm (P.relation j))) =
          sumAlgEquiv R P.rels (Fin n)
            (rename e₀.symm (pderiv (P.map i) (P.relation j)))
        rw [pderiv_sumAlgEquiv]
        congr 1
        have hi : e₀.symm (P.map i) = Sum.inl i := by
          rw [← he₀ i, e₀.symm_apply_apply]
        rw [← hi]
        exact MvPolynomial.pderiv_rename e₀.symm.injective (P.map i) (P.relation j)
      isFinite :=
        { finite_vars := inferInstanceAs (Finite P.rels)
          finite_rels := inferInstanceAs (Finite P.rels) } }
  apply Q'.isStandardSmoothOfRelativeDimension
  change Nat.card P.rels - Nat.card P.rels = 0
  exact Nat.sub_self _

/-- The corresponding factorization of the original actual ring map,
retaining the stronger dimension-zero standard-smooth assertion. -/
theorem ringHom_exists_standardSmoothZero_mvPolynomial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} {n : ℕ} (hf : f.IsStandardSmoothOfRelativeDimension n) :
    ∃ g : MvPolynomial (Fin n) R →+* S,
      g.comp MvPolynomial.C = f ∧ g.IsStandardSmoothOfRelativeDimension 0 := by
  algebraize [f]
  obtain ⟨g, hg⟩ := exists_standardSmoothZero_mvPolynomial n R S
  exact ⟨g.toRingHom, g.comp_algebraMap, hg⟩

/-- A standard-smooth ring map admits the same actual coordinate
factorization for the dimension of one of its finite presentations. -/
theorem ringHom_isStandardSmooth_exists_mvPolynomial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.IsStandardSmooth) :
    ∃ n, ∃ g : MvPolynomial (Fin n) R →+* S,
      g.comp MvPolynomial.C = f ∧ g.IsStandardSmoothOfRelativeDimension 0 := by
  algebraize [f]
  obtain ⟨⟨P⟩⟩ := hf
  letI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension R S := ⟨P, rfl⟩
  exact ⟨P.dimension, ringHom_exists_standardSmoothZero_mvPolynomial
    (f := f) (n := P.dimension)
      (show f.IsStandardSmoothOfRelativeDimension P.dimension from
        ‹Algebra.IsStandardSmoothOfRelativeDimension P.dimension R S›)⟩

/-- The actual map constructed above is étale by the pinned theorem
that standard-smooth algebras of relative dimension zero are étale. -/
theorem exists_etale_mvPolynomial
    (n : ℕ) (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ g : MvPolynomial (Fin n) R →ₐ[R] S,
      @Algebra.Etale (MvPolynomial (Fin n) R) _ S _ g.toRingHom.toAlgebra := by
  obtain ⟨g, hg⟩ := exists_standardSmoothZero_mvPolynomial n R S
  letI := g.toRingHom.toAlgebra
  letI := hg
  exact ⟨g, inferInstance⟩

end KltDP.StandardSmoothCoordinates
