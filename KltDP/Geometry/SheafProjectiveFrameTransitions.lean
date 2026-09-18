/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.SheafFrameRestriction
import KltDP.Geometry.FreeProjectiveBasisTransitions

/-!
# Projective transitions from the original local frames

The two local frames are evaluated in the original module of sections on the
same overlap. Their existing symmetric-Proj comparisons therefore produce
actual projective scheme transitions with the cocycle and original base map.
The polynomial coordinate changes commute with actual sheaf restriction.
This is the algebraic naturality needed to compare projective restriction maps;
it does not assume or assert a whole-Proj base-change construction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry.RelativeSymmetricProj
open KltDP.SymmetricAlgebra

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  {n : ℕ} (b c : Basis (Fin (n + 1)) R M)

/-- The original coordinate change has exactly the original basis coefficients. -/
theorem coordinateChange_X_sum (i : Fin (n + 1)) :
    coordinateChange b c (MvPolynomial.X i) =
      ∑ j : Fin (n + 1), MvPolynomial.C (c.repr (b i) j) * MvPolynomial.X j := by
  rw [coordinateChange_X]
  conv_lhs => rw [← c.sum_repr (b i)]
  simp only [map_sum, map_smul, Algebra.smul_def, map_mul, AlgEquiv.commutes,
    equivMvPolynomial_ι_apply, MvPolynomial.algebraMap_eq]

variable {S N : Type u} [CommRing S] [AddCommGroup N] [Module S N]
  {φ : R →+* S} (b' c' : Basis (Fin (n + 1)) S N)
  (f : M →ₛₗ[φ] N) (hb : ∀ i, f (b i) = b' i) (hc : ∀ i, f (c i) = c' i)

include f hb hc

/-- A semilinear map preserving both original frames preserves their entire
polynomial coordinate change, for the actual coefficient ring homomorphism. -/
theorem coordinateChange_map (p : RelativeProjectiveChart.homogeneousRing R n) :
    MvPolynomial.map φ (coordinateChange b c p) =
      coordinateChange b' c' (MvPolynomial.map φ p) := by
  have h : (MvPolynomial.map φ).comp (coordinateChange b c).toRingHom =
      (coordinateChange b' c').toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change MvPolynomial.map φ (coordinateChange b c (MvPolynomial.C a)) =
        coordinateChange b' c' (MvPolynomial.map φ (MvPolynomial.C a))
      simp only [coordinateChange_C, MvPolynomial.map_C]
    · intro i
      change MvPolynomial.map φ (coordinateChange b c (MvPolynomial.X i)) =
        coordinateChange b' c' (MvPolynomial.map φ (MvPolynomial.X i))
      rw [MvPolynomial.map_X, coordinateChange_X_sum, coordinateChange_X_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
        ← FrameRestrictionDeterminant.repr_restrict c c' f hc (b i) j, hb i]
  exact RingHom.congr_fun h p

end KltDP.Geometry.RelativeSymmetricProj

namespace KltDP.Geometry.SheafFrameRestriction
open KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] overHasWeakSheafify overWEqualsLocallyBijective

variable {X : Scheme.{u}} {M : X.Modules} {n : ℕ}
  (t : KltDP.SheafOfModules.ConstantRankTrivializations
    (R := X.ringCatSheaf) M (n + 1))

/-- The actual change between two sheaf frames on the same original subopen. -/
def projectiveTransition (i j : t.I) (W : X.Opens)
    (hi : W ≤ t.X i) (hj : W ≤ t.X j) :
    RelativeProjectiveChart.freeProjectivization Γ(X, W) n ≅
      RelativeProjectiveChart.freeProjectivization Γ(X, W) n :=
  RelativeSymmetricProj.transition (atlasFrame t i W hi) (atlasFrame t j W hj)

/-- It lies over the original section ring of the actual overlap. -/
@[reassoc] theorem projectiveTransition_toBase (i j : t.I) (W : X.Opens)
    (hi : W ≤ t.X i) (hj : W ≤ t.X j) :
    (projectiveTransition t i j W hi hj).hom ≫
        RelativeProjectiveChart.freeProjectivizationToBase Γ(X, W) n =
      RelativeProjectiveChart.freeProjectivizationToBase Γ(X, W) n :=
  RelativeSymmetricProj.transition_toBase (atlasFrame t i W hi) (atlasFrame t j W hj)

/-- Three actual local frames satisfy the scheme cocycle on their common open. -/
@[reassoc] theorem projectiveTransition_comp (i j k : t.I) (W : X.Opens)
    (hi : W ≤ t.X i) (hj : W ≤ t.X j) (hk : W ≤ t.X k) :
    (projectiveTransition t i j W hi hj).hom ≫
        (projectiveTransition t j k W hj hk).hom =
      (projectiveTransition t i k W hi hk).hom :=
  RelativeSymmetricProj.transition_comp_hom
    (atlasFrame t i W hi) (atlasFrame t j W hj) (atlasFrame t k W hk)

/-- Original polynomial coordinate changes commute with original sheaf
restriction, with no assumed transition naturality. -/
theorem coordinateChange_restrict (i j : t.I) {V W : X.Opens} (hVW : V ≤ W)
    (hi : W ≤ t.X i) (hj : W ≤ t.X j)
    (p : RelativeProjectiveChart.homogeneousRing Γ(X, W) n) :
    MvPolynomial.map (res X hVW)
        (RelativeSymmetricProj.coordinateChange (atlasFrame t i W hi) (atlasFrame t j W hj) p) =
      RelativeSymmetricProj.coordinateChange
        (atlasFrame t i V (hVW.trans hi)) (atlasFrame t j V (hVW.trans hj))
        (MvPolynomial.map (res X hVW) p) :=
  RelativeSymmetricProj.coordinateChange_map
    (atlasFrame t i W hi) (atlasFrame t j W hj)
    (atlasFrame t i V (hVW.trans hi)) (atlasFrame t j V (hVW.trans hj))
    (restrict M hVW) (atlasFrame_restrict t i hVW hi) (atlasFrame_restrict t j hVW hj) p

end KltDP.Geometry.SheafFrameRestriction

#print axioms KltDP.Geometry.RelativeSymmetricProj.coordinateChange_map
#print axioms KltDP.Geometry.SheafFrameRestriction.projectiveTransition_comp
#print axioms KltDP.Geometry.SheafFrameRestriction.coordinateChange_restrict
