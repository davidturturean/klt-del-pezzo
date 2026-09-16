import KltDP.Examples.FrobeniusProjectiveMorphism
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The coordinate-power morphism as the `k`-linear Frobenius of the projective line

The accepted `projectivePowerMorphism p` raises the homogeneous coordinates of the
actual projective line to the `p`-th power while fixing every scalar of `k`; it is a
morphism over `Spec k` (`projectivePowerMorphism_over_base`). This module records the
two remaining identifications required by obligation F28, clause "k-morphism Frobenius":

* on the actual rational point `[1:a]` (the section `pointMorphism a`) the morphism acts
  by `a ↦ a^p`; in characteristic `p` this is the Frobenius `frobenius k p` of the field;
* the absolute Frobenius of the affine and homogeneous coordinate rings factors as the
  coefficient Frobenius `MvPolynomial.map (frobenius k p)` followed by the `k`-linear
  coordinate-power map. Hence the coordinate-power map is the `k`-linear part of the
  absolute Frobenius, and the two are different maps as soon as `k ≠ 𝔽_p`.

The affine coordinate-power map is also identified with Mathlib's `MvPolynomial.expand p`,
which is a `k`-algebra homomorphism by construction.

Only `[Field k]` and `p : ℕ` are needed for the rational-point formula; the Frobenius
identifications need `[Fact p.Prime] [CharP k p]`. No morphism, point or identity is
assumed; everything is derived from the accepted constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusCoordinateFrobenius

open KltDP.Geometry ProjectiveChart FrobeniusProjectivePoints FrobeniusProjectiveMorphism

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- The affine coordinate-power map is Mathlib's `expand p`, hence a `k`-algebra map. -/
theorem affinePowerHom_eq_expand (p : ℕ) :
    affinePowerHom (k := k) p = (MvPolynomial.expand p).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [affinePowerHom_C]
    exact (MvPolynomial.expand_C p r).symm
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [affinePowerHom_X]
    exact (MvPolynomial.expand_X p (0 : Fin 1)).symm

/-- The coordinate-power morphism sends the rational point `[1:a]` to `[1:a^p]`. -/
theorem pointMorphism_projectivePowerMorphism (p : ℕ) (a : k) :
    pointMorphism a ≫ projectivePowerMorphism p = pointMorphism (a ^ p) := by
  have h1 : pointMorphism a =
      Spec.map (CommRingCat.ofHom (parameterEvaluation a)) ≫ parameterMorphism 1 := by
    rw [parameterMorphism_evaluation, pow_one]
  rw [h1, Category.assoc, parameterMorphism_projectivePowerMorphism,
    parameterMorphism_evaluation]

section CharP

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- In characteristic `p`, the coordinate-power morphism acts on rational points by the
Frobenius of the base field. -/
theorem pointMorphism_projectivePowerMorphism_frobenius (a : k) :
    pointMorphism a ≫ projectivePowerMorphism p = pointMorphism (frobenius k p a) :=
  pointMorphism_projectivePowerMorphism p a

/-- The absolute Frobenius of the affine coordinate ring is the coefficient Frobenius
followed by the `k`-linear coordinate-power map. -/
theorem frobenius_affineRing_eq :
    frobenius (affineRing k 1) p =
      (affinePowerHom p).comp (MvPolynomial.map (frobenius k p)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, MvPolynomial.map_C, affinePowerHom_C]
    simp only [frobenius_def]
    exact (MvPolynomial.C_pow r p).symm
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [RingHom.comp_apply, MvPolynomial.map_X, affinePowerHom_X]
    simp only [frobenius_def]

/-- The same factorisation for the homogeneous coordinate ring of the projective line. -/
theorem frobenius_homogeneousRing_eq :
    frobenius (homogeneousRing k 1) p =
      (homogeneousPowerHom p).comp (MvPolynomial.map (frobenius k p)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, MvPolynomial.map_C, homogeneousPowerHom_C]
    simp only [frobenius_def]
    exact (MvPolynomial.C_pow r p).symm
  · intro i
    rw [RingHom.comp_apply, MvPolynomial.map_X, homogeneousPowerHom_X]
    simp only [frobenius_def]

end CharP

end KltDP.Examples.FrobeniusCoordinateFrobenius
