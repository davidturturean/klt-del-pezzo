import KltDP.Geometry.IntersectionPairingSymmetry

/-!
# The numerical space, the Picard rank, and the F14 vocabulary (F02/F07/F14)

Proposition 2.4 needs notions that do not exist in the accepted tree: the Picard rank, torsion-freeness
and unimodularity of `Pic`, and the Noether relation. This module supplies the ones that are definable
today over the **accepted** numerical quotient `NumericalClassGroup X = N¹(X)_ℚ`
(`Geometry/NumericalEquivalence.lean`), and names the rest as `Prop`s a later lane can target, so that
`MinimalResolutionGeometry`'s opaque parameters become statements.

* **The pairing is numerical by construction** (`picardPairing_eq_zero_of_numericallyTrivial_right`
  and `_left`, both unconditional). The E6 mixed form writes `D₁ · D₂ = Σ_C a_C · (C · D₂)`, a finite
  sum of restriction degrees of the *class* of `D₂` (accepted
  `intersectionNumber_eq_picardRestrictionDegree`); if that class is numerically trivial every summand
  vanishes. Symmetry (E7) gives the other argument. **This is why the descent to `N¹` is free**: the
  pairing already factors through numerical equivalence, with no hypothesis at all.
* `picardRank X` is defined unconditionally as `Module.finrank ℚ (N¹(X)_ℚ)`; `Module.finrank` returns
  `0` for an infinite-dimensional space, so the definition only *means* the rank under
  `NumericalSpaceFiniteDimensional`, the named **F07** hypothesis (whose planning source is non-Stacks
  and is deliberately not encoded).
* `PicardTorsionFree`, `PicardUnimodular`, `NoetherRelationFor` are the **F14** clauses as named
  statements. Unimodularity is phrased basis-free — the pairing induces a bijection from `Pic` onto its
  `ℤ`-dual — so that it does not silently presuppose finite-dimensionality. The Noether relation takes
  a Cartier divisor `K` standing for the canonical class, exactly as the accepted
  `AdjunctionFormulaSeed` takes `ω` as a parameter, since no canonical class exists yet (F04, lane D).

Nothing here is proved beyond the numericality of the pairing and the additivity already available;
the point of the rest is vocabulary. (A `picardPairing_congr_right` convenience lemma — numerically
equivalent classes pair equally — was drafted and dropped: it is subsumed by
`picardPairing_eq_zero_of_numericallyTrivial`, and deriving it needs a group-identity juggle on the
multiplicative `Pic` that is cleaner done additively through `Additive Pic`, not with `group`.)
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-! ### The pairing is numerical by construction -/

/-- **Numericality in the second argument**, unconditional: the pairing kills numerically trivial
classes, because the E6 mixed form is a finite sum of restriction degrees of that class. -/
theorem intersectionPairing_eq_zero_of_numericallyTrivial_right
    (D₁ D₂ : CartierDivisor X.toScheme)
    (h : X.NumericallyTrivial (cartierPicardClass X.toScheme D₂)) :
    intersectionPairing X hregular D₁ D₂ = 0 := by
  rw [X.intersectionPairing_eq_weil_sum_right hregular D₁ D₂]
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun C _ => ?_
  dsimp only
  rw [C.intersectionNumber_eq_picardRestrictionDegree D₂, h C, mul_zero]

/-- **Numericality in the first argument**, by the unconditional symmetry of E7. -/
theorem intersectionPairing_eq_zero_of_numericallyTrivial_left
    (D₁ D₂ : CartierDivisor X.toScheme)
    (h : X.NumericallyTrivial (cartierPicardClass X.toScheme D₁)) :
    intersectionPairing X hregular D₁ D₂ = 0 := by
  rw [X.intersectionPairing_symm hregular D₁ D₂]
  exact X.intersectionPairing_eq_zero_of_numericallyTrivial_right hregular D₂ D₁ h

/-- **The Picard pairing kills numerically trivial classes**: the descent of the pairing to the
numerical quotient needs no hypothesis. -/
theorem picardPairing_eq_zero_of_numericallyTrivial (p q : X.toScheme.Pic)
    (h : X.NumericallyTrivial q) : picardPairing X hregular p q = 0 := by
  obtain ⟨D₁, rfl⟩ := cartierPicardClass_surjective X.toScheme p
  obtain ⟨D₂, rfl⟩ := cartierPicardClass_surjective X.toScheme q
  rw [X.picardPairing_class hregular D₁ D₂]
  exact X.intersectionPairing_eq_zero_of_numericallyTrivial_right hregular D₁ D₂ h

/-! ### The numerical space and the Picard rank -/

/-- **The Picard rank** `ρ(X)`, as the dimension of the accepted numerical quotient. `Module.finrank`
returns `0` when the space is not finite-dimensional, so this definition carries its intended meaning
only together with `NumericalSpaceFiniteDimensional`. -/
def picardRank : ℕ := Module.finrank ℚ X.NumericalClassGroup

/-- **Named hypothesis (F07)**: the numerical space is finite-dimensional, which is what makes
`picardRank` the Picard number. The planning entry for this cites a non-Stacks source, which is
deliberately not encoded here. -/
def NumericalSpaceFiniteDimensional : Prop := FiniteDimensional ℚ X.NumericalClassGroup

/-! ### The F14 clauses as named statements -/

/-- **`Pic(X)` is torsion-free** (F14). -/
def PicardTorsionFree : Prop :=
  ∀ (p : Additive X.toScheme.Pic) (n : ℕ), 0 < n → n • p = 0 → p = 0

/-- **`Pic(X)` is unimodular for the intersection pairing** (F14), phrased without a basis: the
pairing induces a bijection from classes onto the `ℤ`-dual of the Picard group. This avoids
presupposing finite-dimensionality. -/
def PicardUnimodular : Prop :=
  Function.Bijective
    (fun p : Additive X.toScheme.Pic =>
      (AddMonoidHom.mk' (fun q : Additive X.toScheme.Pic =>
          picardPairing X hregular p.toMul q.toMul)
        (fun q q' => by
          simpa only [toMul_add] using
            X.picardPairing_mul_right_of_regular hregular p.toMul q.toMul q'.toMul)))

/-- **The Noether relation `K² + ρ = 10`** (F14), with `K` an explicit Cartier divisor standing for
the canonical class, since none exists in the accepted tree (F04, lane D). -/
def NoetherRelationFor (K : CartierDivisor X.toScheme) : Prop :=
  intersectionPairing X hregular K K + (picardRank X : ℤ) = 10

end KltDP.Geometry.NormalProjectiveSurface
